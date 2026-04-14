// Lean compiler output
// Module: Std.Time.Date.PlainDate
// Imports: public import Std.Time.Date.Basic import all Std.Time.Date.Unit.Month import all Std.Time.Date.Unit.Year
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_Day_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Month_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Year_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t, lean_object*);
lean_object* l_Std_Time_Day_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
lean_object* l_Std_Time_Year_Offset_weeks(lean_object*);
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "year"};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value;
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "day"};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__7 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__7_value;
static lean_once_cell_t l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__8;
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "valid"};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__10_value;
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__12_value;
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value;
static lean_once_cell_t l_Std_Time_instReprPlainDate_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__14;
static lean_once_cell_t l_Std_Time_instReprPlainDate_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__15;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__16_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__17 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__17_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__18 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__18_value;
static lean_once_cell_t l_Std_Time_instReprPlainDate_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__19;
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__20 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__21 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__21_value;
static const lean_string_object l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "month"};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__22 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value;
static const lean_ctor_object l_Std_Time_instReprPlainDate_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value)}};
static const lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__23 = (const lean_object*)&l_Std_Time_instReprPlainDate_repr___redArg___closed__23_value;
static lean_once_cell_t l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__24;
static lean_once_cell_t l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainDate_repr___redArg___closed__25;
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprPlainDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprPlainDate_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprPlainDate___closed__0 = (const lean_object*)&l_Std_Time_instReprPlainDate___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprPlainDate = (const lean_object*)&l_Std_Time_instReprPlainDate___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDate_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDate_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDate___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__0;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__1;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__2;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__3;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__4;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__5;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__6;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__7;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__8;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__9;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__10;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__11;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__12;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__13;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__14;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__15;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__16;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__17;
static lean_once_cell_t l_Std_Time_instInhabitedPlainDate___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainDate___closed__18;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedPlainDate;
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainDate___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__0 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__0_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainDate___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__1 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__1_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainDate___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__2 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__2_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Year_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__3 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__3_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Month_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__4 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__4_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Day_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__5 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__5_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__3_value),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__0_value)} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__6 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__6_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__4_value),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__1_value)} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__7 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__7_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__5_value),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__2_value)} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__8 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__8_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareLex___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__7_value),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__8_value)} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__9 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__9_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareLex___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__6_value),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__9_value)} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__10 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__10_value;
LEAN_EXPORT const lean_object* l_Std_Time_instOrdPlainDate = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__10_value;
static lean_once_cell_t l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instInhabited;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDay_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12;
static lean_once_cell_t l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_weekOfMonth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfMonth___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_rollOver___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_rollOver___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_rollOver___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_rollOver___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_rollOver___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_rollOver___closed__2;
static lean_once_cell_t l_Std_Time_PlainDate_rollOver___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_rollOver___closed__3;
static lean_once_cell_t l_Std_Time_PlainDate_rollOver___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_rollOver___closed__4;
static lean_once_cell_t l_Std_Time_PlainDate_rollOver___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_rollOver___closed__5;
static lean_once_cell_t l_Std_Time_PlainDate_rollOver___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_rollOver___closed__6;
static lean_once_cell_t l_Std_Time_PlainDate_rollOver___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_rollOver___closed__7;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthRollOver(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_weekday___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekday___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_weekday___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekday___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_weekday___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekday___closed__2;
static lean_once_cell_t l_Std_Time_PlainDate_weekday___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekday___closed__3;
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekday___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_addDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instHAddOffset = (const lean_object*)&l_Std_Time_PlainDate_instHAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDate_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_subDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instHSubOffset = (const lean_object*)&l_Std_Time_PlainDate_instHSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_addWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instHAddOffset__1___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instHAddOffset__1 = (const lean_object*)&l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_subWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instHSubOffset__1___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instHSubOffset__1 = (const lean_object*)&l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value;
static lean_object* _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(7u);
v___x_15_ = lean_nat_to_int(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__0));
v___x_24_ = lean_string_length(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__14, &l_Std_Time_instReprPlainDate_repr___redArg___closed__14_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__14);
v___x_26_ = lean_nat_to_int(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(8u);
v___x_35_ = lean_nat_to_int(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(9u);
v___x_43_ = lean_nat_to_int(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_nat_to_int(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate_repr___redArg(lean_object* v_x_46_){
_start:
{
lean_object* v_year_47_; lean_object* v_month_48_; lean_object* v_day_49_; lean_object* v___x_50_; uint8_t v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___y_89_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_year_47_ = lean_ctor_get(v_x_46_, 0);
v_month_48_ = lean_ctor_get(v_x_46_, 1);
v_day_49_ = lean_ctor_get(v_x_46_, 2);
v___x_50_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__5));
v___x_86_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__18));
v___x_87_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__19, &l_Std_Time_instReprPlainDate_repr___redArg___closed__19_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__19);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_112_ = lean_int_dec_lt(v_year_47_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = l_Int_repr(v_year_47_);
v___x_114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
v___y_89_ = v___x_114_;
goto v___jp_88_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = l_Int_repr(v_year_47_);
v___x_116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
v___x_117_ = l_Repr_addAppParen(v___x_116_, v___x_110_);
v___y_89_ = v___x_117_;
goto v___jp_88_;
}
v___jp_51_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_inc(v___y_53_);
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___y_53_);
lean_ctor_set(v___x_58_, 1, v___y_57_);
v___x_59_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v___y_52_);
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___y_55_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
lean_inc_n(v___y_56_, 2);
v___x_61_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___y_56_);
lean_inc_n(v___y_54_, 2);
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___y_54_);
v___x_63_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__7));
v___x_64_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_50_);
v___x_66_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = l_Std_Time_Day_instReprOrdinal___lam__0(v_day_49_, v___x_67_);
v___x_69_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_66_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___y_52_);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_65_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___y_56_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___y_54_);
v___x_74_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__10));
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_50_);
v___x_77_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__12));
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__15, &l_Std_Time_instReprPlainDate_repr___redArg___closed__15_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__15);
v___x_80_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__16));
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_78_);
v___x_82_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__17));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_79_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___y_52_);
return v___x_85_;
}
v___jp_88_:
{
lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_90_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_87_);
lean_ctor_set(v___x_90_, 1, v___y_89_);
v___x_91_ = 0;
v___x_92_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*1, v___x_91_);
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_86_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__21));
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = lean_box(1);
v___x_97_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_95_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = ((lean_object*)(l_Std_Time_instReprPlainDate_repr___redArg___closed__23));
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_50_);
v___x_101_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_104_ = lean_int_dec_lt(v_month_48_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = l_Int_repr(v_month_48_);
v___x_106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
v___y_52_ = v___x_91_;
v___y_53_ = v___x_101_;
v___y_54_ = v___x_96_;
v___y_55_ = v___x_100_;
v___y_56_ = v___x_94_;
v___y_57_ = v___x_106_;
goto v___jp_51_;
}
else
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = l_Int_repr(v_month_48_);
v___x_108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
v___x_109_ = l_Repr_addAppParen(v___x_108_, v___x_102_);
v___y_52_ = v___x_91_;
v___y_53_ = v___x_101_;
v___y_54_ = v___x_96_;
v___y_55_ = v___x_100_;
v___y_56_ = v___x_94_;
v___y_57_ = v___x_109_;
goto v___jp_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate_repr___redArg___boxed(lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_Time_instReprPlainDate_repr___redArg(v_x_118_);
lean_dec_ref(v_x_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate_repr(lean_object* v_x_120_, lean_object* v_prec_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Std_Time_instReprPlainDate_repr___redArg(v_x_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainDate_repr___boxed(lean_object* v_x_123_, lean_object* v_prec_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Time_instReprPlainDate_repr(v_x_123_, v_prec_124_);
lean_dec(v_prec_124_);
lean_dec_ref(v_x_123_);
return v_res_125_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDate_decEq(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
lean_object* v_year_130_; lean_object* v_month_131_; lean_object* v_day_132_; lean_object* v_year_133_; lean_object* v_month_134_; lean_object* v_day_135_; uint8_t v___x_136_; 
v_year_130_ = lean_ctor_get(v_x_128_, 0);
v_month_131_ = lean_ctor_get(v_x_128_, 1);
v_day_132_ = lean_ctor_get(v_x_128_, 2);
v_year_133_ = lean_ctor_get(v_x_129_, 0);
v_month_134_ = lean_ctor_get(v_x_129_, 1);
v_day_135_ = lean_ctor_get(v_x_129_, 2);
v___x_136_ = lean_int_dec_eq(v_year_130_, v_year_133_);
if (v___x_136_ == 0)
{
return v___x_136_;
}
else
{
uint8_t v___x_137_; 
v___x_137_ = lean_int_dec_eq(v_month_131_, v_month_134_);
if (v___x_137_ == 0)
{
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = lean_int_dec_eq(v_day_132_, v_day_135_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDate_decEq___boxed(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_139_, v_x_140_);
lean_dec_ref(v_x_140_);
lean_dec_ref(v_x_139_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainDate(lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
uint8_t v___x_145_; 
v___x_145_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_143_, v_x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDate___boxed(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Std_Time_instDecidableEqPlainDate(v_x_146_, v_x_147_);
lean_dec_ref(v_x_147_);
lean_dec_ref(v_x_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__0(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__1(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(11u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__2(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__1, &l_Std_Time_instInhabitedPlainDate___closed__1_once, _init_l_Std_Time_instInhabitedPlainDate___closed__1);
v___x_155_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_156_ = lean_int_add(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__3(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_158_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__2, &l_Std_Time_instInhabitedPlainDate___closed__2_once, _init_l_Std_Time_instInhabitedPlainDate___closed__2);
v___x_159_ = lean_int_sub(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__4(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_range_162_; 
v___x_160_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_161_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__3, &l_Std_Time_instInhabitedPlainDate___closed__3_once, _init_l_Std_Time_instInhabitedPlainDate___closed__3);
v_range_162_ = lean_int_add(v___x_161_, v___x_160_);
return v_range_162_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__5(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_164_ = lean_int_sub(v___x_163_, v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__6(void){
_start:
{
lean_object* v_range_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_range_165_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__4, &l_Std_Time_instInhabitedPlainDate___closed__4_once, _init_l_Std_Time_instInhabitedPlainDate___closed__4);
v___x_166_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_167_ = lean_int_emod(v___x_166_, v_range_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__7(void){
_start:
{
lean_object* v_range_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_range_168_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__4, &l_Std_Time_instInhabitedPlainDate___closed__4_once, _init_l_Std_Time_instInhabitedPlainDate___closed__4);
v___x_169_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__6, &l_Std_Time_instInhabitedPlainDate___closed__6_once, _init_l_Std_Time_instInhabitedPlainDate___closed__6);
v___x_170_ = lean_int_add(v___x_169_, v_range_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__8(void){
_start:
{
lean_object* v_range_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_range_171_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__4, &l_Std_Time_instInhabitedPlainDate___closed__4_once, _init_l_Std_Time_instInhabitedPlainDate___closed__4);
v___x_172_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__7, &l_Std_Time_instInhabitedPlainDate___closed__7_once, _init_l_Std_Time_instInhabitedPlainDate___closed__7);
v___x_173_ = lean_int_emod(v___x_172_, v_range_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__9(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_175_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__8, &l_Std_Time_instInhabitedPlainDate___closed__8_once, _init_l_Std_Time_instInhabitedPlainDate___closed__8);
v___x_176_ = lean_int_add(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__10(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(30u);
v___x_178_ = lean_nat_to_int(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__11(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__10, &l_Std_Time_instInhabitedPlainDate___closed__10_once, _init_l_Std_Time_instInhabitedPlainDate___closed__10);
v___x_180_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_181_ = lean_int_add(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__12(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_183_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__11, &l_Std_Time_instInhabitedPlainDate___closed__11_once, _init_l_Std_Time_instInhabitedPlainDate___closed__11);
v___x_184_ = lean_int_sub(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__13(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v_range_187_; 
v___x_185_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_186_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__12, &l_Std_Time_instInhabitedPlainDate___closed__12_once, _init_l_Std_Time_instInhabitedPlainDate___closed__12);
v_range_187_ = lean_int_add(v___x_186_, v___x_185_);
return v_range_187_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__14(void){
_start:
{
lean_object* v_range_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_range_188_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__13, &l_Std_Time_instInhabitedPlainDate___closed__13_once, _init_l_Std_Time_instInhabitedPlainDate___closed__13);
v___x_189_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_190_ = lean_int_emod(v___x_189_, v_range_188_);
return v___x_190_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__15(void){
_start:
{
lean_object* v_range_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_range_191_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__13, &l_Std_Time_instInhabitedPlainDate___closed__13_once, _init_l_Std_Time_instInhabitedPlainDate___closed__13);
v___x_192_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__14, &l_Std_Time_instInhabitedPlainDate___closed__14_once, _init_l_Std_Time_instInhabitedPlainDate___closed__14);
v___x_193_ = lean_int_add(v___x_192_, v_range_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__16(void){
_start:
{
lean_object* v_range_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_range_194_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__13, &l_Std_Time_instInhabitedPlainDate___closed__13_once, _init_l_Std_Time_instInhabitedPlainDate___closed__13);
v___x_195_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__15, &l_Std_Time_instInhabitedPlainDate___closed__15_once, _init_l_Std_Time_instInhabitedPlainDate___closed__15);
v___x_196_ = lean_int_emod(v___x_195_, v_range_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__17(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_198_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__16, &l_Std_Time_instInhabitedPlainDate___closed__16_once, _init_l_Std_Time_instInhabitedPlainDate___closed__16);
v___x_199_ = lean_int_add(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__18(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_200_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__17, &l_Std_Time_instInhabitedPlainDate___closed__17_once, _init_l_Std_Time_instInhabitedPlainDate___closed__17);
v___x_201_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__9, &l_Std_Time_instInhabitedPlainDate___closed__9_once, _init_l_Std_Time_instInhabitedPlainDate___closed__9);
v___x_202_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_201_);
lean_ctor_set(v___x_203_, 2, v___x_200_);
return v___x_203_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__18, &l_Std_Time_instInhabitedPlainDate___closed__18_once, _init_l_Std_Time_instInhabitedPlainDate___closed__18);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0(lean_object* v_x_205_){
_start:
{
lean_object* v_year_206_; 
v_year_206_ = lean_ctor_get(v_x_205_, 0);
lean_inc(v_year_206_);
return v_year_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0___boxed(lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Time_instOrdPlainDate___lam__0(v_x_207_);
lean_dec_ref(v_x_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1(lean_object* v_x_209_){
_start:
{
lean_object* v_month_210_; 
v_month_210_ = lean_ctor_get(v_x_209_, 1);
lean_inc(v_month_210_);
return v_month_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1___boxed(lean_object* v_x_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_Time_instOrdPlainDate___lam__1(v_x_211_);
lean_dec_ref(v_x_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2(lean_object* v_x_213_){
_start:
{
lean_object* v_day_214_; 
v_day_214_ = lean_ctor_get(v_x_213_, 2);
lean_inc(v_day_214_);
return v_day_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2___boxed(lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_Time_instOrdPlainDate___lam__2(v_x_215_);
lean_dec_ref(v_x_215_);
return v_res_216_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(4u);
v___x_240_ = lean_nat_to_int(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(400u);
v___x_242_ = lean_nat_to_int(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(100u);
v___x_244_ = lean_nat_to_int(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip(lean_object* v_year_245_, lean_object* v_month_246_, lean_object* v_day_247_){
_start:
{
uint8_t v___y_249_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_261_; 
v___x_254_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_255_ = lean_int_mod(v_year_245_, v___x_254_);
v___x_256_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_261_ = lean_int_dec_eq(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
if (v___x_261_ == 0)
{
v___y_249_ = v___x_261_;
goto v___jp_248_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_263_ = lean_int_mod(v_year_245_, v___x_262_);
v___x_264_ = lean_int_dec_eq(v___x_263_, v___x_256_);
lean_dec(v___x_263_);
if (v___x_264_ == 0)
{
if (v___x_261_ == 0)
{
goto v___jp_257_;
}
else
{
v___y_249_ = v___x_261_;
goto v___jp_248_;
}
}
else
{
goto v___jp_257_;
}
}
v___jp_248_:
{
lean_object* v_max_250_; uint8_t v___x_251_; 
v_max_250_ = l_Std_Time_Month_Ordinal_days(v___y_249_, v_month_246_);
v___x_251_ = lean_int_dec_lt(v_max_250_, v_day_247_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec(v_max_250_);
v___x_252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_252_, 0, v_year_245_);
lean_ctor_set(v___x_252_, 1, v_month_246_);
lean_ctor_set(v___x_252_, 2, v_day_247_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; 
lean_dec(v_day_247_);
v___x_253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_253_, 0, v_year_245_);
lean_ctor_set(v___x_253_, 1, v_month_246_);
lean_ctor_set(v___x_253_, 2, v_max_250_);
return v___x_253_;
}
}
v___jp_257_:
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_259_ = lean_int_mod(v_year_245_, v___x_258_);
v___x_260_ = lean_int_dec_eq(v___x_259_, v___x_256_);
lean_dec(v___x_259_);
v___y_249_ = v___x_260_;
goto v___jp_248_;
}
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_265_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__17, &l_Std_Time_instInhabitedPlainDate___closed__17_once, _init_l_Std_Time_instInhabitedPlainDate___closed__17);
v___x_266_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__9, &l_Std_Time_instInhabitedPlainDate___closed__9_once, _init_l_Std_Time_instInhabitedPlainDate___closed__9);
v___x_267_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
lean_ctor_set(v___x_268_, 2, v___x_265_);
return v___x_268_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited(void){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Std_Time_PlainDate_instInhabited___closed__0, &l_Std_Time_PlainDate_instInhabited___closed__0_once, _init_l_Std_Time_PlainDate_instInhabited___closed__0);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDay_x3f(lean_object* v_year_270_, lean_object* v_month_271_, lean_object* v_day_272_){
_start:
{
uint8_t v___y_274_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_287_; 
v___x_280_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_281_ = lean_int_mod(v_year_270_, v___x_280_);
v___x_282_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_287_ = lean_int_dec_eq(v___x_281_, v___x_282_);
lean_dec(v___x_281_);
if (v___x_287_ == 0)
{
v___y_274_ = v___x_287_;
goto v___jp_273_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_288_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_289_ = lean_int_mod(v_year_270_, v___x_288_);
v___x_290_ = lean_int_dec_eq(v___x_289_, v___x_282_);
lean_dec(v___x_289_);
if (v___x_290_ == 0)
{
if (v___x_287_ == 0)
{
goto v___jp_283_;
}
else
{
v___y_274_ = v___x_287_;
goto v___jp_273_;
}
}
else
{
goto v___jp_283_;
}
}
v___jp_273_:
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = l_Std_Time_Month_Ordinal_days(v___y_274_, v_month_271_);
v___x_276_ = lean_int_dec_le(v_day_272_, v___x_275_);
lean_dec(v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_dec(v_day_272_);
lean_dec(v_month_271_);
lean_dec(v_year_270_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_278_, 0, v_year_270_);
lean_ctor_set(v___x_278_, 1, v_month_271_);
lean_ctor_set(v___x_278_, 2, v_day_272_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
v___jp_283_:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_284_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_285_ = lean_int_mod(v_year_270_, v___x_284_);
v___x_286_ = lean_int_dec_eq(v___x_285_, v___x_282_);
lean_dec(v___x_285_);
v___y_274_ = v___x_286_;
goto v___jp_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal(lean_object* v_year_291_, lean_object* v_ordinal_292_){
_start:
{
uint8_t v___y_294_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_306_; 
v___x_299_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_300_ = lean_int_mod(v_year_291_, v___x_299_);
v___x_301_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_306_ = lean_int_dec_eq(v___x_300_, v___x_301_);
lean_dec(v___x_300_);
if (v___x_306_ == 0)
{
v___y_294_ = v___x_306_;
goto v___jp_293_;
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_308_ = lean_int_mod(v_year_291_, v___x_307_);
v___x_309_ = lean_int_dec_eq(v___x_308_, v___x_301_);
lean_dec(v___x_308_);
if (v___x_309_ == 0)
{
if (v___x_306_ == 0)
{
goto v___jp_302_;
}
else
{
v___y_294_ = v___x_306_;
goto v___jp_293_;
}
}
else
{
goto v___jp_302_;
}
}
v___jp_293_:
{
lean_object* v_val_295_; lean_object* v_fst_296_; lean_object* v_snd_297_; lean_object* v___x_298_; 
v_val_295_ = l_Std_Time_ValidDate_ofOrdinal(v___y_294_, v_ordinal_292_);
v_fst_296_ = lean_ctor_get(v_val_295_, 0);
lean_inc(v_fst_296_);
v_snd_297_ = lean_ctor_get(v_val_295_, 1);
lean_inc(v_snd_297_);
lean_dec_ref(v_val_295_);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v_year_291_);
lean_ctor_set(v___x_298_, 1, v_fst_296_);
lean_ctor_set(v___x_298_, 2, v_snd_297_);
return v___x_298_;
}
v___jp_302_:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_303_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_304_ = lean_int_mod(v_year_291_, v___x_303_);
v___x_305_ = lean_int_dec_eq(v___x_304_, v___x_301_);
lean_dec(v___x_304_);
v___y_294_ = v___x_305_;
goto v___jp_293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal___boxed(lean_object* v_year_310_, lean_object* v_ordinal_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Time_PlainDate_ofYearOrdinal(v_year_310_, v_ordinal_311_);
lean_dec(v_ordinal_311_);
return v_res_312_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(719468u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(31u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(12u);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(146097u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1460u);
v___x_322_ = lean_nat_to_int(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(36524u);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(146096u);
v___x_326_ = lean_nat_to_int(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(365u);
v___x_328_ = lean_nat_to_int(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(5u);
v___x_330_ = lean_nat_to_int(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(2u);
v___x_332_ = lean_nat_to_int(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(153u);
v___x_334_ = lean_nat_to_int(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(10u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___x_338_ = lean_int_neg(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(3u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object* v_day_341_){
_start:
{
lean_object* v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; uint8_t v___y_346_; lean_object* v___x_351_; lean_object* v_z_352_; lean_object* v___x_353_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_409_; uint8_t v___x_452_; 
v___x_351_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0);
v_z_352_ = lean_int_add(v_day_341_, v___x_351_);
v___x_353_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_452_ = lean_int_dec_le(v___x_353_, v_z_352_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6);
v___x_454_ = lean_int_sub(v_z_352_, v___x_453_);
v___y_409_ = v___x_454_;
goto v___jp_408_;
}
else
{
lean_inc(v_z_352_);
v___y_409_ = v_z_352_;
goto v___jp_408_;
}
v___jp_342_:
{
lean_object* v_max_347_; uint8_t v___x_348_; 
v_max_347_ = l_Std_Time_Month_Ordinal_days(v___y_346_, v___y_344_);
v___x_348_ = lean_int_dec_lt(v_max_347_, v___y_345_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec(v_max_347_);
v___x_349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_349_, 0, v___y_343_);
lean_ctor_set(v___x_349_, 1, v___y_344_);
lean_ctor_set(v___x_349_, 2, v___y_345_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; 
lean_dec(v___y_345_);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v___y_343_);
lean_ctor_set(v___x_350_, 1, v___y_344_);
lean_ctor_set(v___x_350_, 2, v_max_347_);
return v___x_350_;
}
}
v___jp_354_:
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = lean_int_mod(v___y_357_, v___y_355_);
v___x_360_ = lean_int_dec_eq(v___x_359_, v___x_353_);
lean_dec(v___x_359_);
v___y_343_ = v___y_357_;
v___y_344_ = v___y_356_;
v___y_345_ = v___y_358_;
v___y_346_ = v___x_360_;
goto v___jp_342_;
}
v___jp_361_:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_int_mod(v___y_364_, v___y_365_);
v___x_369_ = lean_int_dec_eq(v___x_368_, v___x_353_);
lean_dec(v___x_368_);
if (v___x_369_ == 0)
{
v___y_343_ = v___y_364_;
v___y_344_ = v___y_363_;
v___y_345_ = v___y_367_;
v___y_346_ = v___x_369_;
goto v___jp_342_;
}
else
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_int_mod(v___y_364_, v___y_366_);
v___x_371_ = lean_int_dec_eq(v___x_370_, v___x_353_);
lean_dec(v___x_370_);
if (v___x_371_ == 0)
{
if (v___x_369_ == 0)
{
v___y_355_ = v___y_362_;
v___y_356_ = v___y_363_;
v___y_357_ = v___y_364_;
v___y_358_ = v___y_367_;
goto v___jp_354_;
}
else
{
v___y_343_ = v___y_364_;
v___y_344_ = v___y_363_;
v___y_345_ = v___y_367_;
v___y_346_ = v___x_369_;
goto v___jp_342_;
}
}
else
{
v___y_355_ = v___y_362_;
v___y_356_ = v___y_363_;
v___y_357_ = v___y_364_;
v___y_358_ = v___y_367_;
goto v___jp_354_;
}
}
}
v___jp_372_:
{
uint8_t v___x_380_; 
v___x_380_ = lean_int_dec_le(v___y_378_, v___y_374_);
if (v___x_380_ == 0)
{
lean_dec(v___y_374_);
lean_inc(v___y_378_);
v___y_362_ = v___y_373_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_375_;
v___y_365_ = v___y_376_;
v___y_366_ = v___y_377_;
v___y_367_ = v___y_378_;
goto v___jp_361_;
}
else
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1);
v___x_382_ = lean_int_dec_le(v___y_374_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec(v___y_374_);
v___y_362_ = v___y_373_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_375_;
v___y_365_ = v___y_376_;
v___y_366_ = v___y_377_;
v___y_367_ = v___x_381_;
goto v___jp_361_;
}
else
{
v___y_362_ = v___y_373_;
v___y_363_ = v___y_379_;
v___y_364_ = v___y_375_;
v___y_365_ = v___y_376_;
v___y_366_ = v___y_377_;
v___y_367_ = v___y_374_;
goto v___jp_361_;
}
}
}
v___jp_383_:
{
lean_object* v_y_392_; uint8_t v___x_393_; 
v_y_392_ = lean_int_add(v___y_389_, v___y_391_);
lean_dec(v___y_389_);
v___x_393_ = lean_int_dec_le(v___y_390_, v___y_385_);
if (v___x_393_ == 0)
{
lean_dec(v___y_385_);
lean_inc(v___y_390_);
v___y_373_ = v___y_384_;
v___y_374_ = v___y_386_;
v___y_375_ = v_y_392_;
v___y_376_ = v___y_387_;
v___y_377_ = v___y_388_;
v___y_378_ = v___y_390_;
v___y_379_ = v___y_390_;
goto v___jp_372_;
}
else
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_395_ = lean_int_dec_le(v___y_385_, v___x_394_);
if (v___x_395_ == 0)
{
lean_dec(v___y_385_);
v___y_373_ = v___y_384_;
v___y_374_ = v___y_386_;
v___y_375_ = v_y_392_;
v___y_376_ = v___y_387_;
v___y_377_ = v___y_388_;
v___y_378_ = v___y_390_;
v___y_379_ = v___x_394_;
goto v___jp_372_;
}
else
{
v___y_373_ = v___y_384_;
v___y_374_ = v___y_386_;
v___y_375_ = v_y_392_;
v___y_376_ = v___y_387_;
v___y_377_ = v___y_388_;
v___y_378_ = v___y_390_;
v___y_379_ = v___y_385_;
goto v___jp_372_;
}
}
}
v___jp_396_:
{
lean_object* v_m_406_; uint8_t v___x_407_; 
v_m_406_ = lean_int_add(v___y_400_, v___y_405_);
lean_dec(v___y_400_);
v___x_407_ = lean_int_dec_le(v_m_406_, v___y_397_);
if (v___x_407_ == 0)
{
v___y_384_ = v___y_398_;
v___y_385_ = v_m_406_;
v___y_386_ = v___y_399_;
v___y_387_ = v___y_401_;
v___y_388_ = v___y_402_;
v___y_389_ = v___y_403_;
v___y_390_ = v___y_404_;
v___y_391_ = v___x_353_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___y_398_;
v___y_385_ = v_m_406_;
v___y_386_ = v___y_399_;
v___y_387_ = v___y_401_;
v___y_388_ = v___y_402_;
v___y_389_ = v___y_403_;
v___y_390_ = v___y_404_;
v___y_391_ = v___y_404_;
goto v___jp_383_;
}
}
v___jp_408_:
{
lean_object* v___x_410_; lean_object* v_era_411_; lean_object* v___x_412_; lean_object* v_doe_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_yoe_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_y_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_doy_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_mp_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_d_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_410_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3);
v_era_411_ = lean_int_div(v___y_409_, v___x_410_);
lean_dec(v___y_409_);
v___x_412_ = lean_int_mul(v_era_411_, v___x_410_);
v_doe_413_ = lean_int_sub(v_z_352_, v___x_412_);
lean_dec(v___x_412_);
lean_dec(v_z_352_);
v___x_414_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4);
v___x_415_ = lean_int_div(v_doe_413_, v___x_414_);
v___x_416_ = lean_int_sub(v_doe_413_, v___x_415_);
lean_dec(v___x_415_);
v___x_417_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5);
v___x_418_ = lean_int_div(v_doe_413_, v___x_417_);
v___x_419_ = lean_int_add(v___x_416_, v___x_418_);
lean_dec(v___x_418_);
lean_dec(v___x_416_);
v___x_420_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6);
v___x_421_ = lean_int_div(v_doe_413_, v___x_420_);
v___x_422_ = lean_int_sub(v___x_419_, v___x_421_);
lean_dec(v___x_421_);
lean_dec(v___x_419_);
v___x_423_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7);
v_yoe_424_ = lean_int_div(v___x_422_, v___x_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_426_ = lean_int_mul(v_era_411_, v___x_425_);
lean_dec(v_era_411_);
v_y_427_ = lean_int_add(v_yoe_424_, v___x_426_);
lean_dec(v___x_426_);
v___x_428_ = lean_int_mul(v___x_423_, v_yoe_424_);
v___x_429_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_430_ = lean_int_div(v_yoe_424_, v___x_429_);
v___x_431_ = lean_int_add(v___x_428_, v___x_430_);
lean_dec(v___x_430_);
lean_dec(v___x_428_);
v___x_432_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_433_ = lean_int_div(v_yoe_424_, v___x_432_);
lean_dec(v_yoe_424_);
v___x_434_ = lean_int_sub(v___x_431_, v___x_433_);
lean_dec(v___x_433_);
lean_dec(v___x_431_);
v_doy_435_ = lean_int_sub(v_doe_413_, v___x_434_);
lean_dec(v___x_434_);
lean_dec(v_doe_413_);
v___x_436_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8);
v___x_437_ = lean_int_mul(v___x_436_, v_doy_435_);
v___x_438_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9);
v___x_439_ = lean_int_add(v___x_437_, v___x_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10);
v_mp_441_ = lean_int_div(v___x_439_, v___x_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_int_mul(v___x_440_, v_mp_441_);
v___x_443_ = lean_int_add(v___x_442_, v___x_438_);
lean_dec(v___x_442_);
v___x_444_ = lean_int_div(v___x_443_, v___x_436_);
lean_dec(v___x_443_);
v___x_445_ = lean_int_sub(v_doy_435_, v___x_444_);
lean_dec(v___x_444_);
lean_dec(v_doy_435_);
v___x_446_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_d_447_ = lean_int_add(v___x_445_, v___x_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11);
v___x_449_ = lean_int_dec_lt(v_mp_441_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; 
v___x_450_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12);
v___y_397_ = v___x_438_;
v___y_398_ = v___x_425_;
v___y_399_ = v_d_447_;
v___y_400_ = v_mp_441_;
v___y_401_ = v___x_429_;
v___y_402_ = v___x_432_;
v___y_403_ = v_y_427_;
v___y_404_ = v___x_446_;
v___y_405_ = v___x_450_;
goto v___jp_396_;
}
else
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13);
v___y_397_ = v___x_438_;
v___y_398_ = v___x_425_;
v___y_399_ = v_d_447_;
v___y_400_ = v_mp_441_;
v___y_401_ = v___x_429_;
v___y_402_ = v___x_432_;
v___y_403_ = v_y_427_;
v___y_404_ = v___x_446_;
v___y_405_ = v___x_451_;
goto v___jp_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___boxed(lean_object* v_day_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v_day_455_);
lean_dec(v_day_455_);
return v_res_456_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfMonth___closed__0(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_458_ = lean_int_neg(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object* v_date_459_){
_start:
{
lean_object* v_day_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_day_460_ = lean_ctor_get(v_date_459_, 2);
v___x_461_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_462_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_463_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v___x_464_ = lean_int_add(v_day_460_, v___x_463_);
v___x_465_ = lean_int_ediv(v___x_464_, v___x_462_);
lean_dec(v___x_464_);
v___x_466_ = lean_int_add(v___x_465_, v___x_461_);
lean_dec(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object* v_date_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Time_PlainDate_weekOfMonth(v_date_467_);
lean_dec_ref(v_date_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object* v_date_469_){
_start:
{
lean_object* v_month_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_month_470_ = lean_ctor_get(v_date_469_, 1);
v___x_471_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_472_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13);
v___x_473_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v___x_474_ = lean_int_add(v_month_470_, v___x_473_);
v___x_475_ = lean_int_ediv(v___x_474_, v___x_472_);
lean_dec(v___x_474_);
v___x_476_ = lean_int_add(v___x_475_, v___x_471_);
lean_dec(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object* v_date_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Std_Time_PlainDate_quarter(v_date_477_);
lean_dec_ref(v_date_477_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object* v_date_479_){
_start:
{
lean_object* v_year_480_; lean_object* v_month_481_; lean_object* v_day_482_; uint8_t v___y_484_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_494_; 
v_year_480_ = lean_ctor_get(v_date_479_, 0);
v_month_481_ = lean_ctor_get(v_date_479_, 1);
v_day_482_ = lean_ctor_get(v_date_479_, 2);
v___x_487_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_488_ = lean_int_mod(v_year_480_, v___x_487_);
v___x_489_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_494_ = lean_int_dec_eq(v___x_488_, v___x_489_);
lean_dec(v___x_488_);
if (v___x_494_ == 0)
{
v___y_484_ = v___x_494_;
goto v___jp_483_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_496_ = lean_int_mod(v_year_480_, v___x_495_);
v___x_497_ = lean_int_dec_eq(v___x_496_, v___x_489_);
lean_dec(v___x_496_);
if (v___x_497_ == 0)
{
if (v___x_494_ == 0)
{
goto v___jp_490_;
}
else
{
v___y_484_ = v___x_494_;
goto v___jp_483_;
}
}
else
{
goto v___jp_490_;
}
}
v___jp_483_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_inc(v_day_482_);
lean_inc(v_month_481_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_month_481_);
lean_ctor_set(v___x_485_, 1, v_day_482_);
v___x_486_ = l_Std_Time_ValidDate_dayOfYear(v___y_484_, v___x_485_);
lean_dec_ref(v___x_485_);
return v___x_486_;
}
v___jp_490_:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_492_ = lean_int_mod(v_year_480_, v___x_491_);
v___x_493_ = lean_int_dec_eq(v___x_492_, v___x_489_);
lean_dec(v___x_492_);
v___y_484_ = v___x_493_;
goto v___jp_483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object* v_date_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Time_PlainDate_dayOfYear(v_date_498_);
lean_dec_ref(v_date_498_);
return v_res_499_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_era(lean_object* v_date_500_){
_start:
{
lean_object* v_year_501_; uint8_t v___x_502_; 
v_year_501_ = lean_ctor_get(v_date_500_, 0);
v___x_502_ = l_Std_Time_Year_Offset_era(v_year_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object* v_date_503_){
_start:
{
uint8_t v_res_504_; lean_object* v_r_505_; 
v_res_504_ = l_Std_Time_PlainDate_era(v_date_503_);
lean_dec_ref(v_date_503_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object* v_date_506_){
_start:
{
lean_object* v_year_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_515_; 
v_year_507_ = lean_ctor_get(v_date_506_, 0);
v___x_508_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_509_ = lean_int_mod(v_year_507_, v___x_508_);
v___x_510_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_515_ = lean_int_dec_eq(v___x_509_, v___x_510_);
lean_dec(v___x_509_);
if (v___x_515_ == 0)
{
return v___x_515_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_516_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_517_ = lean_int_mod(v_year_507_, v___x_516_);
v___x_518_ = lean_int_dec_eq(v___x_517_, v___x_510_);
lean_dec(v___x_517_);
if (v___x_518_ == 0)
{
if (v___x_515_ == 0)
{
goto v___jp_511_;
}
else
{
return v___x_515_;
}
}
else
{
goto v___jp_511_;
}
}
v___jp_511_:
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_513_ = lean_int_mod(v_year_507_, v___x_512_);
v___x_514_ = lean_int_dec_eq(v___x_513_, v___x_510_);
lean_dec(v___x_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object* v_date_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Std_Time_PlainDate_inLeapYear(v_date_519_);
lean_dec_ref(v_date_519_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13);
v___x_523_ = lean_int_neg(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_unsigned_to_nat(399u);
v___x_525_ = lean_nat_to_int(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object* v_date_526_){
_start:
{
lean_object* v_year_527_; lean_object* v_month_528_; lean_object* v_day_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_570_; uint8_t v___x_575_; 
v_year_527_ = lean_ctor_get(v_date_526_, 0);
lean_inc(v_year_527_);
v_month_528_ = lean_ctor_get(v_date_526_, 1);
lean_inc(v_month_528_);
v_day_529_ = lean_ctor_get(v_date_526_, 2);
lean_inc(v_day_529_);
lean_dec_ref(v_date_526_);
v___x_530_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9);
v___x_531_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_575_ = lean_int_dec_lt(v___x_530_, v_month_528_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_int_sub(v_year_527_, v___x_531_);
lean_dec(v_year_527_);
v___y_570_ = v___x_576_;
goto v___jp_569_;
}
else
{
v___y_570_ = v_year_527_;
goto v___jp_569_;
}
v___jp_532_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_doy_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_doe_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_537_ = lean_int_add(v_month_528_, v___y_536_);
lean_dec(v_month_528_);
v___x_538_ = lean_int_mul(v___y_535_, v___x_537_);
lean_dec(v___x_537_);
v___x_539_ = lean_int_add(v___x_538_, v___x_530_);
lean_dec(v___x_538_);
v___x_540_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8);
v___x_541_ = lean_int_div(v___x_539_, v___x_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_int_add(v___x_541_, v_day_529_);
lean_dec(v_day_529_);
lean_dec(v___x_541_);
v_doy_543_ = lean_int_sub(v___x_542_, v___x_531_);
lean_dec(v___x_542_);
v___x_544_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7);
v___x_545_ = lean_int_mul(v___y_534_, v___x_544_);
v___x_546_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_547_ = lean_int_div(v___y_534_, v___x_546_);
v___x_548_ = lean_int_add(v___x_545_, v___x_547_);
lean_dec(v___x_547_);
lean_dec(v___x_545_);
v___x_549_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_550_ = lean_int_div(v___y_534_, v___x_549_);
lean_dec(v___y_534_);
v___x_551_ = lean_int_sub(v___x_548_, v___x_550_);
lean_dec(v___x_550_);
lean_dec(v___x_548_);
v_doe_552_ = lean_int_add(v___x_551_, v_doy_543_);
lean_dec(v_doy_543_);
lean_dec(v___x_551_);
v___x_553_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3);
v___x_554_ = lean_int_mul(v___y_533_, v___x_553_);
lean_dec(v___y_533_);
v___x_555_ = lean_int_add(v___x_554_, v_doe_552_);
lean_dec(v_doe_552_);
lean_dec(v___x_554_);
v___x_556_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0);
v___x_557_ = lean_int_sub(v___x_555_, v___x_556_);
lean_dec(v___x_555_);
return v___x_557_;
}
v___jp_558_:
{
lean_object* v___x_561_; lean_object* v_era_562_; lean_object* v___x_563_; lean_object* v_yoe_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_561_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v_era_562_ = lean_int_div(v___y_560_, v___x_561_);
lean_dec(v___y_560_);
v___x_563_ = lean_int_mul(v_era_562_, v___x_561_);
v_yoe_564_ = lean_int_sub(v___y_559_, v___x_563_);
lean_dec(v___x_563_);
lean_dec(v___y_559_);
v___x_565_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10);
v___x_566_ = lean_int_dec_lt(v___x_530_, v_month_528_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___y_533_ = v_era_562_;
v___y_534_ = v_yoe_564_;
v___y_535_ = v___x_565_;
v___y_536_ = v___x_567_;
goto v___jp_532_;
}
else
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0, &l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0_once, _init_l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0);
v___y_533_ = v_era_562_;
v___y_534_ = v_yoe_564_;
v___y_535_ = v___x_565_;
v___y_536_ = v___x_568_;
goto v___jp_532_;
}
}
v___jp_569_:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_572_ = lean_int_dec_le(v___x_571_, v___y_570_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1, &l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1_once, _init_l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1);
v___x_574_ = lean_int_sub(v___y_570_, v___x_573_);
v___y_559_ = v___y_570_;
v___y_560_ = v___x_574_;
goto v___jp_558_;
}
else
{
lean_inc(v___y_570_);
v___y_559_ = v___y_570_;
v___y_560_ = v___y_570_;
goto v___jp_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays(lean_object* v_date_577_, lean_object* v_days_578_){
_start:
{
lean_object* v_dateDays_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_dateDays_579_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_577_);
v___x_580_ = lean_int_add(v_dateDays_579_, v_days_578_);
lean_dec(v_dateDays_579_);
v___x_581_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_580_);
lean_dec(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays___boxed(lean_object* v_date_582_, lean_object* v_days_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Std_Time_PlainDate_addDays(v_date_582_, v_days_583_);
lean_dec(v_days_583_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays(lean_object* v_date_585_, lean_object* v_days_586_){
_start:
{
lean_object* v___x_587_; lean_object* v_dateDays_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_int_neg(v_days_586_);
v_dateDays_588_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_585_);
v___x_589_ = lean_int_add(v_dateDays_588_, v___x_587_);
lean_dec(v___x_587_);
lean_dec(v_dateDays_588_);
v___x_590_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_589_);
lean_dec(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays___boxed(lean_object* v_date_591_, lean_object* v_days_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_Time_PlainDate_subDays(v_date_591_, v_days_592_);
lean_dec(v_days_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks(lean_object* v_date_594_, lean_object* v_weeks_595_){
_start:
{
lean_object* v_dateDays_596_; lean_object* v___x_597_; lean_object* v_daysToAdd_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_dateDays_596_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_594_);
v___x_597_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_598_ = lean_int_mul(v_weeks_595_, v___x_597_);
v___x_599_ = lean_int_add(v_dateDays_596_, v_daysToAdd_598_);
lean_dec(v_daysToAdd_598_);
lean_dec(v_dateDays_596_);
v___x_600_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_599_);
lean_dec(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks___boxed(lean_object* v_date_601_, lean_object* v_weeks_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_Time_PlainDate_addWeeks(v_date_601_, v_weeks_602_);
lean_dec(v_weeks_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks(lean_object* v_date_604_, lean_object* v_weeks_605_){
_start:
{
lean_object* v___x_606_; lean_object* v_dateDays_607_; lean_object* v___x_608_; lean_object* v_daysToAdd_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_606_ = lean_int_neg(v_weeks_605_);
v_dateDays_607_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_604_);
v___x_608_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_609_ = lean_int_mul(v___x_606_, v___x_608_);
lean_dec(v___x_606_);
v___x_610_ = lean_int_add(v_dateDays_607_, v_daysToAdd_609_);
lean_dec(v_daysToAdd_609_);
lean_dec(v_dateDays_607_);
v___x_611_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_610_);
lean_dec(v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks___boxed(lean_object* v_date_612_, lean_object* v_weeks_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Time_PlainDate_subWeeks(v_date_612_, v_weeks_613_);
lean_dec(v_weeks_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object* v_date_615_, lean_object* v_months_616_){
_start:
{
lean_object* v_year_617_; lean_object* v_month_618_; lean_object* v_day_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_652_; 
v_year_617_ = lean_ctor_get(v_date_615_, 0);
v_month_618_ = lean_ctor_get(v_date_615_, 1);
v_day_619_ = lean_ctor_get(v_date_615_, 2);
v_isSharedCheck_652_ = !lean_is_exclusive(v_date_615_);
if (v_isSharedCheck_652_ == 0)
{
v___x_621_ = v_date_615_;
v_isShared_622_ = v_isSharedCheck_652_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_day_619_);
lean_inc(v_month_618_);
lean_inc(v_year_617_);
lean_dec(v_date_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_652_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_totalMonths_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v_wrappedMonths_628_; lean_object* v_yearsOffset_629_; lean_object* v___x_630_; uint8_t v___y_632_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_648_; 
v___x_623_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_624_ = lean_int_sub(v_month_618_, v___x_623_);
lean_dec(v_month_618_);
v_totalMonths_625_ = lean_int_add(v___x_624_, v_months_616_);
lean_dec(v___x_624_);
v___x_626_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_627_ = lean_int_emod(v_totalMonths_625_, v___x_626_);
v_wrappedMonths_628_ = lean_int_add(v___x_627_, v___x_623_);
lean_dec(v___x_627_);
v_yearsOffset_629_ = lean_int_ediv(v_totalMonths_625_, v___x_626_);
lean_dec(v_totalMonths_625_);
v___x_630_ = lean_int_add(v_year_617_, v_yearsOffset_629_);
lean_dec(v_yearsOffset_629_);
lean_dec(v_year_617_);
v___x_641_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_642_ = lean_int_mod(v___x_630_, v___x_641_);
v___x_643_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_648_ = lean_int_dec_eq(v___x_642_, v___x_643_);
lean_dec(v___x_642_);
if (v___x_648_ == 0)
{
v___y_632_ = v___x_648_;
goto v___jp_631_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_650_ = lean_int_mod(v___x_630_, v___x_649_);
v___x_651_ = lean_int_dec_eq(v___x_650_, v___x_643_);
lean_dec(v___x_650_);
if (v___x_651_ == 0)
{
if (v___x_648_ == 0)
{
goto v___jp_644_;
}
else
{
v___y_632_ = v___x_648_;
goto v___jp_631_;
}
}
else
{
goto v___jp_644_;
}
}
v___jp_631_:
{
lean_object* v_max_633_; uint8_t v___x_634_; 
v_max_633_ = l_Std_Time_Month_Ordinal_days(v___y_632_, v_wrappedMonths_628_);
v___x_634_ = lean_int_dec_lt(v_max_633_, v_day_619_);
if (v___x_634_ == 0)
{
lean_object* v___x_636_; 
lean_dec(v_max_633_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v_wrappedMonths_628_);
lean_ctor_set(v___x_621_, 0, v___x_630_);
v___x_636_ = v___x_621_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_wrappedMonths_628_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_day_619_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_639_; 
lean_dec(v_day_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 2, v_max_633_);
lean_ctor_set(v___x_621_, 1, v_wrappedMonths_628_);
lean_ctor_set(v___x_621_, 0, v___x_630_);
v___x_639_ = v___x_621_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_wrappedMonths_628_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_max_633_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
v___jp_644_:
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_645_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_646_ = lean_int_mod(v___x_630_, v___x_645_);
v___x_647_ = lean_int_dec_eq(v___x_646_, v___x_643_);
lean_dec(v___x_646_);
v___y_632_ = v___x_647_;
goto v___jp_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip___boxed(lean_object* v_date_653_, lean_object* v_months_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Std_Time_PlainDate_addMonthsClip(v_date_653_, v_months_654_);
lean_dec(v_months_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip(lean_object* v_date_656_, lean_object* v_months_657_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_int_neg(v_months_657_);
v___x_659_ = l_Std_Time_PlainDate_addMonthsClip(v_date_656_, v___x_658_);
lean_dec(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip___boxed(lean_object* v_date_660_, lean_object* v_months_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_Time_PlainDate_subMonthsClip(v_date_660_, v_months_661_);
lean_dec(v_months_661_);
return v_res_662_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__0(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(30u);
v___x_664_ = lean_nat_to_int(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__1(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__0, &l_Std_Time_PlainDate_rollOver___closed__0_once, _init_l_Std_Time_PlainDate_rollOver___closed__0);
v___x_666_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_667_ = lean_int_add(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__2(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_669_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__1, &l_Std_Time_PlainDate_rollOver___closed__1_once, _init_l_Std_Time_PlainDate_rollOver___closed__1);
v___x_670_ = lean_int_sub(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__3(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_range_673_; 
v___x_671_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_672_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__2, &l_Std_Time_PlainDate_rollOver___closed__2_once, _init_l_Std_Time_PlainDate_rollOver___closed__2);
v_range_673_ = lean_int_add(v___x_672_, v___x_671_);
return v_range_673_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__4(void){
_start:
{
lean_object* v_range_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_range_674_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_675_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_676_ = lean_int_emod(v___x_675_, v_range_674_);
return v___x_676_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__5(void){
_start:
{
lean_object* v_range_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_range_677_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_678_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__4, &l_Std_Time_PlainDate_rollOver___closed__4_once, _init_l_Std_Time_PlainDate_rollOver___closed__4);
v___x_679_ = lean_int_add(v___x_678_, v_range_677_);
return v___x_679_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__6(void){
_start:
{
lean_object* v_range_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_range_680_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_681_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__5, &l_Std_Time_PlainDate_rollOver___closed__5_once, _init_l_Std_Time_PlainDate_rollOver___closed__5);
v___x_682_ = lean_int_emod(v___x_681_, v_range_680_);
return v___x_682_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__7(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_684_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__6, &l_Std_Time_PlainDate_rollOver___closed__6_once, _init_l_Std_Time_PlainDate_rollOver___closed__6);
v___x_685_ = lean_int_add(v___x_684_, v___x_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver(lean_object* v_year_686_, lean_object* v_month_687_, lean_object* v_day_688_){
_start:
{
lean_object* v___y_690_; lean_object* v___x_696_; uint8_t v___y_698_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_710_; 
v___x_696_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_703_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_704_ = lean_int_mod(v_year_686_, v___x_703_);
v___x_705_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_710_ = lean_int_dec_eq(v___x_704_, v___x_705_);
lean_dec(v___x_704_);
if (v___x_710_ == 0)
{
v___y_698_ = v___x_710_;
goto v___jp_697_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_712_ = lean_int_mod(v_year_686_, v___x_711_);
v___x_713_ = lean_int_dec_eq(v___x_712_, v___x_705_);
lean_dec(v___x_712_);
if (v___x_713_ == 0)
{
if (v___x_710_ == 0)
{
goto v___jp_706_;
}
else
{
v___y_698_ = v___x_710_;
goto v___jp_697_;
}
}
else
{
goto v___jp_706_;
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_dateDays_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_691_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_692_ = lean_int_sub(v_day_688_, v___x_691_);
v_dateDays_693_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v___y_690_);
v___x_694_ = lean_int_add(v_dateDays_693_, v___x_692_);
lean_dec(v___x_692_);
lean_dec(v_dateDays_693_);
v___x_695_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_694_);
lean_dec(v___x_694_);
return v___x_695_;
}
v___jp_697_:
{
lean_object* v_max_699_; uint8_t v___x_700_; 
v_max_699_ = l_Std_Time_Month_Ordinal_days(v___y_698_, v_month_687_);
v___x_700_ = lean_int_dec_lt(v_max_699_, v___x_696_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
lean_dec(v_max_699_);
v___x_701_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_701_, 0, v_year_686_);
lean_ctor_set(v___x_701_, 1, v_month_687_);
lean_ctor_set(v___x_701_, 2, v___x_696_);
v___y_690_ = v___x_701_;
goto v___jp_689_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_702_, 0, v_year_686_);
lean_ctor_set(v___x_702_, 1, v_month_687_);
lean_ctor_set(v___x_702_, 2, v_max_699_);
v___y_690_ = v___x_702_;
goto v___jp_689_;
}
}
v___jp_706_:
{
lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_707_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_708_ = lean_int_mod(v_year_686_, v___x_707_);
v___x_709_ = lean_int_dec_eq(v___x_708_, v___x_705_);
lean_dec(v___x_708_);
v___y_698_ = v___x_709_;
goto v___jp_697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver___boxed(lean_object* v_year_714_, lean_object* v_month_715_, lean_object* v_day_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_Time_PlainDate_rollOver(v_year_714_, v_month_715_, v_day_716_);
lean_dec(v_day_716_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip(lean_object* v_dt_718_, lean_object* v_year_719_){
_start:
{
lean_object* v_month_720_; lean_object* v_day_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_746_; 
v_month_720_ = lean_ctor_get(v_dt_718_, 1);
v_day_721_ = lean_ctor_get(v_dt_718_, 2);
v_isSharedCheck_746_ = !lean_is_exclusive(v_dt_718_);
if (v_isSharedCheck_746_ == 0)
{
lean_object* v_unused_747_; 
v_unused_747_ = lean_ctor_get(v_dt_718_, 0);
lean_dec(v_unused_747_);
v___x_723_ = v_dt_718_;
v_isShared_724_ = v_isSharedCheck_746_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_day_721_);
lean_inc(v_month_720_);
lean_dec(v_dt_718_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_746_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
uint8_t v___y_726_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_742_; 
v___x_735_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_736_ = lean_int_mod(v_year_719_, v___x_735_);
v___x_737_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_742_ = lean_int_dec_eq(v___x_736_, v___x_737_);
lean_dec(v___x_736_);
if (v___x_742_ == 0)
{
v___y_726_ = v___x_742_;
goto v___jp_725_;
}
else
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_744_ = lean_int_mod(v_year_719_, v___x_743_);
v___x_745_ = lean_int_dec_eq(v___x_744_, v___x_737_);
lean_dec(v___x_744_);
if (v___x_745_ == 0)
{
if (v___x_742_ == 0)
{
goto v___jp_738_;
}
else
{
v___y_726_ = v___x_742_;
goto v___jp_725_;
}
}
else
{
goto v___jp_738_;
}
}
v___jp_725_:
{
lean_object* v_max_727_; uint8_t v___x_728_; 
v_max_727_ = l_Std_Time_Month_Ordinal_days(v___y_726_, v_month_720_);
v___x_728_ = lean_int_dec_lt(v_max_727_, v_day_721_);
if (v___x_728_ == 0)
{
lean_object* v___x_730_; 
lean_dec(v_max_727_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_year_719_);
v___x_730_ = v___x_723_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_year_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_month_720_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_day_721_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
else
{
lean_object* v___x_733_; 
lean_dec(v_day_721_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 2, v_max_727_);
lean_ctor_set(v___x_723_, 0, v_year_719_);
v___x_733_ = v___x_723_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_year_719_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_month_720_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_max_727_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
v___jp_738_:
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_739_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_740_ = lean_int_mod(v_year_719_, v___x_739_);
v___x_741_ = lean_int_dec_eq(v___x_740_, v___x_737_);
lean_dec(v___x_740_);
v___y_726_ = v___x_741_;
goto v___jp_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearRollOver(lean_object* v_dt_748_, lean_object* v_year_749_){
_start:
{
lean_object* v_month_750_; lean_object* v_day_751_; lean_object* v___x_752_; 
v_month_750_ = lean_ctor_get(v_dt_748_, 1);
lean_inc(v_month_750_);
v_day_751_ = lean_ctor_get(v_dt_748_, 2);
lean_inc(v_day_751_);
lean_dec_ref(v_dt_748_);
v___x_752_ = l_Std_Time_PlainDate_rollOver(v_year_749_, v_month_750_, v_day_751_);
lean_dec(v_day_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object* v_date_753_, lean_object* v_months_754_){
_start:
{
lean_object* v_year_755_; lean_object* v_month_756_; lean_object* v_day_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_791_; 
v_year_755_ = lean_ctor_get(v_date_753_, 0);
v_month_756_ = lean_ctor_get(v_date_753_, 1);
v_day_757_ = lean_ctor_get(v_date_753_, 2);
v_isSharedCheck_791_ = !lean_is_exclusive(v_date_753_);
if (v_isSharedCheck_791_ == 0)
{
v___x_759_ = v_date_753_;
v_isShared_760_ = v_isSharedCheck_791_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_day_757_);
lean_inc(v_month_756_);
lean_inc(v_year_755_);
lean_dec(v_date_753_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_791_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___y_762_; lean_object* v___x_769_; uint8_t v___y_771_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_787_; 
v___x_769_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_780_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_781_ = lean_int_mod(v_year_755_, v___x_780_);
v___x_782_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_787_ = lean_int_dec_eq(v___x_781_, v___x_782_);
lean_dec(v___x_781_);
if (v___x_787_ == 0)
{
v___y_771_ = v___x_787_;
goto v___jp_770_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_789_ = lean_int_mod(v_year_755_, v___x_788_);
v___x_790_ = lean_int_dec_eq(v___x_789_, v___x_782_);
lean_dec(v___x_789_);
if (v___x_790_ == 0)
{
if (v___x_787_ == 0)
{
goto v___jp_783_;
}
else
{
v___y_771_ = v___x_787_;
goto v___jp_770_;
}
}
else
{
goto v___jp_783_;
}
}
v___jp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_dateDays_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_763_ = l_Std_Time_PlainDate_addMonthsClip(v___y_762_, v_months_754_);
v___x_764_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_765_ = lean_int_sub(v_day_757_, v___x_764_);
lean_dec(v_day_757_);
v_dateDays_766_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v___x_763_);
v___x_767_ = lean_int_add(v_dateDays_766_, v___x_765_);
lean_dec(v___x_765_);
lean_dec(v_dateDays_766_);
v___x_768_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_767_);
lean_dec(v___x_767_);
return v___x_768_;
}
v___jp_770_:
{
lean_object* v_max_772_; uint8_t v___x_773_; 
v_max_772_ = l_Std_Time_Month_Ordinal_days(v___y_771_, v_month_756_);
v___x_773_ = lean_int_dec_lt(v_max_772_, v___x_769_);
if (v___x_773_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v_max_772_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 2, v___x_769_);
v___x_775_ = v___x_759_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_year_755_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_month_756_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v___x_769_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
v___y_762_ = v___x_775_;
goto v___jp_761_;
}
}
else
{
lean_object* v___x_778_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 2, v_max_772_);
v___x_778_ = v___x_759_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_year_755_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_month_756_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_max_772_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
v___y_762_ = v___x_778_;
goto v___jp_761_;
}
}
}
v___jp_783_:
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_785_ = lean_int_mod(v_year_755_, v___x_784_);
v___x_786_ = lean_int_dec_eq(v___x_785_, v___x_782_);
lean_dec(v___x_785_);
v___y_771_ = v___x_786_;
goto v___jp_770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver___boxed(lean_object* v_date_792_, lean_object* v_months_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_792_, v_months_793_);
lean_dec(v_months_793_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver(lean_object* v_date_795_, lean_object* v_months_796_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_int_neg(v_months_796_);
v___x_798_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_795_, v___x_797_);
lean_dec(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver___boxed(lean_object* v_date_799_, lean_object* v_months_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_Time_PlainDate_subMonthsRollOver(v_date_799_, v_months_800_);
lean_dec(v_months_800_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver(lean_object* v_date_802_, lean_object* v_years_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_805_ = lean_int_mul(v_years_803_, v___x_804_);
v___x_806_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_802_, v___x_805_);
lean_dec(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver___boxed(lean_object* v_date_807_, lean_object* v_years_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_Time_PlainDate_addYearsRollOver(v_date_807_, v_years_808_);
lean_dec(v_years_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver(lean_object* v_date_810_, lean_object* v_years_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_812_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_813_ = lean_int_mul(v_years_811_, v___x_812_);
v___x_814_ = lean_int_neg(v___x_813_);
lean_dec(v___x_813_);
v___x_815_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_810_, v___x_814_);
lean_dec(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver___boxed(lean_object* v_date_816_, lean_object* v_years_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_Time_PlainDate_subYearsRollOver(v_date_816_, v_years_817_);
lean_dec(v_years_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip(lean_object* v_date_819_, lean_object* v_years_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_822_ = lean_int_mul(v_years_820_, v___x_821_);
v___x_823_ = l_Std_Time_PlainDate_addMonthsClip(v_date_819_, v___x_822_);
lean_dec(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip___boxed(lean_object* v_date_824_, lean_object* v_years_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Time_PlainDate_addYearsClip(v_date_824_, v_years_825_);
lean_dec(v_years_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip(lean_object* v_date_827_, lean_object* v_years_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_830_ = lean_int_mul(v_years_828_, v___x_829_);
v___x_831_ = lean_int_neg(v___x_830_);
lean_dec(v___x_830_);
v___x_832_ = l_Std_Time_PlainDate_addMonthsClip(v_date_827_, v___x_831_);
lean_dec(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip___boxed(lean_object* v_date_833_, lean_object* v_years_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_Time_PlainDate_subYearsClip(v_date_833_, v_years_834_);
lean_dec(v_years_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip(lean_object* v_dt_836_, lean_object* v_days_837_){
_start:
{
lean_object* v_year_838_; lean_object* v_month_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_864_; 
v_year_838_ = lean_ctor_get(v_dt_836_, 0);
v_month_839_ = lean_ctor_get(v_dt_836_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_dt_836_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v_dt_836_, 2);
lean_dec(v_unused_865_);
v___x_841_ = v_dt_836_;
v_isShared_842_ = v_isSharedCheck_864_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_month_839_);
lean_inc(v_year_838_);
lean_dec(v_dt_836_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_864_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
uint8_t v___y_844_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_860_; 
v___x_853_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_854_ = lean_int_mod(v_year_838_, v___x_853_);
v___x_855_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_860_ = lean_int_dec_eq(v___x_854_, v___x_855_);
lean_dec(v___x_854_);
if (v___x_860_ == 0)
{
v___y_844_ = v___x_860_;
goto v___jp_843_;
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_862_ = lean_int_mod(v_year_838_, v___x_861_);
v___x_863_ = lean_int_dec_eq(v___x_862_, v___x_855_);
lean_dec(v___x_862_);
if (v___x_863_ == 0)
{
if (v___x_860_ == 0)
{
goto v___jp_856_;
}
else
{
v___y_844_ = v___x_860_;
goto v___jp_843_;
}
}
else
{
goto v___jp_856_;
}
}
v___jp_843_:
{
lean_object* v_max_845_; uint8_t v___x_846_; 
v_max_845_ = l_Std_Time_Month_Ordinal_days(v___y_844_, v_month_839_);
v___x_846_ = lean_int_dec_lt(v_max_845_, v_days_837_);
if (v___x_846_ == 0)
{
lean_object* v___x_848_; 
lean_dec(v_max_845_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 2, v_days_837_);
v___x_848_ = v___x_841_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_year_838_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_month_839_);
lean_ctor_set(v_reuseFailAlloc_849_, 2, v_days_837_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
else
{
lean_object* v___x_851_; 
lean_dec(v_days_837_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 2, v_max_845_);
v___x_851_ = v___x_841_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_year_838_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_month_839_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_max_845_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
v___jp_856_:
{
lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_857_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_858_ = lean_int_mod(v_year_838_, v___x_857_);
v___x_859_ = lean_int_dec_eq(v___x_858_, v___x_855_);
lean_dec(v___x_858_);
v___y_844_ = v___x_859_;
goto v___jp_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver(lean_object* v_dt_866_, lean_object* v_days_867_){
_start:
{
lean_object* v_year_868_; lean_object* v_month_869_; lean_object* v___x_870_; 
v_year_868_ = lean_ctor_get(v_dt_866_, 0);
lean_inc(v_year_868_);
v_month_869_ = lean_ctor_get(v_dt_866_, 1);
lean_inc(v_month_869_);
lean_dec_ref(v_dt_866_);
v___x_870_ = l_Std_Time_PlainDate_rollOver(v_year_868_, v_month_869_, v_days_867_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver___boxed(lean_object* v_dt_871_, lean_object* v_days_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_Time_PlainDate_withDaysRollOver(v_dt_871_, v_days_872_);
lean_dec(v_days_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip(lean_object* v_dt_874_, lean_object* v_month_875_){
_start:
{
lean_object* v_year_876_; lean_object* v_day_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_902_; 
v_year_876_ = lean_ctor_get(v_dt_874_, 0);
v_day_877_ = lean_ctor_get(v_dt_874_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_dt_874_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_dt_874_, 1);
lean_dec(v_unused_903_);
v___x_879_ = v_dt_874_;
v_isShared_880_ = v_isSharedCheck_902_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_day_877_);
lean_inc(v_year_876_);
lean_dec(v_dt_874_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_902_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
uint8_t v___y_882_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_898_; 
v___x_891_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_892_ = lean_int_mod(v_year_876_, v___x_891_);
v___x_893_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_898_ = lean_int_dec_eq(v___x_892_, v___x_893_);
lean_dec(v___x_892_);
if (v___x_898_ == 0)
{
v___y_882_ = v___x_898_;
goto v___jp_881_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_899_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_900_ = lean_int_mod(v_year_876_, v___x_899_);
v___x_901_ = lean_int_dec_eq(v___x_900_, v___x_893_);
lean_dec(v___x_900_);
if (v___x_901_ == 0)
{
if (v___x_898_ == 0)
{
goto v___jp_894_;
}
else
{
v___y_882_ = v___x_898_;
goto v___jp_881_;
}
}
else
{
goto v___jp_894_;
}
}
v___jp_881_:
{
lean_object* v_max_883_; uint8_t v___x_884_; 
v_max_883_ = l_Std_Time_Month_Ordinal_days(v___y_882_, v_month_875_);
v___x_884_ = lean_int_dec_lt(v_max_883_, v_day_877_);
if (v___x_884_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v_max_883_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v_month_875_);
v___x_886_ = v___x_879_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_year_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_month_875_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_day_877_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v_day_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 2, v_max_883_);
lean_ctor_set(v___x_879_, 1, v_month_875_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_year_876_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_month_875_);
lean_ctor_set(v_reuseFailAlloc_890_, 2, v_max_883_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
v___jp_894_:
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_895_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_896_ = lean_int_mod(v_year_876_, v___x_895_);
v___x_897_ = lean_int_dec_eq(v___x_896_, v___x_893_);
lean_dec(v___x_896_);
v___y_882_ = v___x_897_;
goto v___jp_881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthRollOver(lean_object* v_dt_904_, lean_object* v_month_905_){
_start:
{
lean_object* v_year_906_; lean_object* v_day_907_; lean_object* v___x_908_; 
v_year_906_ = lean_ctor_get(v_dt_904_, 0);
lean_inc(v_year_906_);
v_day_907_ = lean_ctor_get(v_dt_904_, 2);
lean_inc(v_day_907_);
lean_dec_ref(v_dt_904_);
v___x_908_ = l_Std_Time_PlainDate_rollOver(v_year_906_, v_month_905_, v_day_907_);
lean_dec(v_day_907_);
return v___x_908_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__0(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_910_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_911_ = lean_int_sub(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__1(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_range_914_; 
v___x_912_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_913_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__0, &l_Std_Time_PlainDate_weekday___closed__0_once, _init_l_Std_Time_PlainDate_weekday___closed__0);
v_range_914_ = lean_int_add(v___x_913_, v___x_912_);
return v_range_914_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__2(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_916_ = lean_int_neg(v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__3(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_unsigned_to_nat(6u);
v___x_918_ = lean_nat_to_int(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_weekday(lean_object* v_date_919_){
_start:
{
lean_object* v___y_921_; lean_object* v_days_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_days_930_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_919_);
v___x_931_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_932_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__2, &l_Std_Time_PlainDate_weekday___closed__2_once, _init_l_Std_Time_PlainDate_weekday___closed__2);
v___x_933_ = lean_int_dec_le(v___x_932_, v_days_930_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_934_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8);
v___x_935_ = lean_int_add(v_days_930_, v___x_934_);
lean_dec(v_days_930_);
v___x_936_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_937_ = lean_int_emod(v___x_935_, v___x_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__3, &l_Std_Time_PlainDate_weekday___closed__3_once, _init_l_Std_Time_PlainDate_weekday___closed__3);
v___x_939_ = lean_int_add(v___x_937_, v___x_938_);
lean_dec(v___x_937_);
v___y_921_ = v___x_939_;
goto v___jp_920_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_int_add(v_days_930_, v___x_931_);
lean_dec(v_days_930_);
v___x_941_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_942_ = lean_int_emod(v___x_940_, v___x_941_);
lean_dec(v___x_940_);
v___y_921_ = v___x_942_;
goto v___jp_920_;
}
v___jp_920_:
{
lean_object* v___x_922_; lean_object* v_range_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_922_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_range_923_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__1, &l_Std_Time_PlainDate_weekday___closed__1_once, _init_l_Std_Time_PlainDate_weekday___closed__1);
v___x_924_ = lean_int_sub(v___y_921_, v___x_922_);
lean_dec(v___y_921_);
v___x_925_ = lean_int_emod(v___x_924_, v_range_923_);
lean_dec(v___x_924_);
v___x_926_ = lean_int_add(v___x_925_, v_range_923_);
lean_dec(v___x_925_);
v___x_927_ = lean_int_emod(v___x_926_, v_range_923_);
lean_dec(v___x_926_);
v___x_928_ = lean_int_add(v___x_927_, v___x_922_);
lean_dec(v___x_927_);
v___x_929_ = l_Std_Time_Weekday_ofOrdinal(v___x_928_);
lean_dec(v___x_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekday___boxed(lean_object* v_date_943_){
_start:
{
uint8_t v_res_944_; lean_object* v_r_945_; 
v_res_944_ = l_Std_Time_PlainDate_weekday(v_date_943_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object* v_date_946_){
_start:
{
lean_object* v_year_947_; lean_object* v_month_948_; lean_object* v_day_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_987_; 
v_year_947_ = lean_ctor_get(v_date_946_, 0);
v_month_948_ = lean_ctor_get(v_date_946_, 1);
v_day_949_ = lean_ctor_get(v_date_946_, 2);
v_isSharedCheck_987_ = !lean_is_exclusive(v_date_946_);
if (v_isSharedCheck_987_ == 0)
{
v___x_951_ = v_date_946_;
v_isShared_952_ = v_isSharedCheck_987_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_day_949_);
lean_inc(v_month_948_);
lean_inc(v_year_947_);
lean_dec(v_date_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_987_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___y_956_; lean_object* v___x_965_; uint8_t v___y_967_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_983_; 
v___x_953_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_954_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_965_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_976_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_977_ = lean_int_mod(v_year_947_, v___x_976_);
v___x_978_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_983_ = lean_int_dec_eq(v___x_977_, v___x_978_);
lean_dec(v___x_977_);
if (v___x_983_ == 0)
{
v___y_967_ = v___x_983_;
goto v___jp_966_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_984_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_985_ = lean_int_mod(v_year_947_, v___x_984_);
v___x_986_ = lean_int_dec_eq(v___x_985_, v___x_978_);
lean_dec(v___x_985_);
if (v___x_986_ == 0)
{
if (v___x_983_ == 0)
{
goto v___jp_979_;
}
else
{
v___y_967_ = v___x_983_;
goto v___jp_966_;
}
}
else
{
goto v___jp_979_;
}
}
v___jp_955_:
{
uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_957_ = l_Std_Time_PlainDate_weekday(v___y_956_);
v___x_958_ = l_Std_Time_Weekday_toOrdinal(v___x_957_);
v___x_959_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v___x_960_ = lean_int_add(v___x_958_, v___x_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_int_add(v_day_949_, v___x_959_);
lean_dec(v_day_949_);
v___x_962_ = lean_int_add(v___x_961_, v___x_960_);
lean_dec(v___x_960_);
lean_dec(v___x_961_);
v___x_963_ = lean_int_ediv(v___x_962_, v___x_954_);
lean_dec(v___x_962_);
v___x_964_ = lean_int_add(v___x_963_, v___x_953_);
lean_dec(v___x_963_);
return v___x_964_;
}
v___jp_966_:
{
lean_object* v_max_968_; uint8_t v___x_969_; 
v_max_968_ = l_Std_Time_Month_Ordinal_days(v___y_967_, v_month_948_);
v___x_969_ = lean_int_dec_lt(v_max_968_, v___x_965_);
if (v___x_969_ == 0)
{
lean_object* v___x_971_; 
lean_dec(v_max_968_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 2, v___x_965_);
v___x_971_ = v___x_951_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_year_947_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_month_948_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v___x_965_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
v___y_956_ = v___x_971_;
goto v___jp_955_;
}
}
else
{
lean_object* v___x_974_; 
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 2, v_max_968_);
v___x_974_ = v___x_951_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_year_947_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v_month_948_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_max_968_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
v___y_956_ = v___x_974_;
goto v___jp_955_;
}
}
}
v___jp_979_:
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_981_ = lean_int_mod(v_year_947_, v___x_980_);
v___x_982_ = lean_int_dec_eq(v___x_981_, v___x_978_);
lean_dec(v___x_981_);
v___y_967_ = v___x_982_;
goto v___jp_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday(lean_object* v_date_988_, uint8_t v_desiredWeekday_989_){
_start:
{
lean_object* v___y_991_; uint8_t v___x_995_; lean_object* v_weekday_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
lean_inc_ref(v_date_988_);
v___x_995_ = l_Std_Time_PlainDate_weekday(v_date_988_);
v_weekday_996_ = l_Std_Time_Weekday_toOrdinal(v___x_995_);
v___x_997_ = l_Std_Time_Weekday_toOrdinal(v_desiredWeekday_989_);
v___x_998_ = lean_int_neg(v_weekday_996_);
lean_dec(v_weekday_996_);
v___x_999_ = lean_int_add(v___x_997_, v___x_998_);
lean_dec(v___x_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1001_ = lean_int_dec_lt(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
v___y_991_ = v___x_999_;
goto v___jp_990_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1003_ = lean_int_add(v___x_999_, v___x_1002_);
lean_dec(v___x_999_);
v___y_991_ = v___x_1003_;
goto v___jp_990_;
}
v___jp_990_:
{
lean_object* v_dateDays_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_dateDays_992_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_988_);
v___x_993_ = lean_int_add(v_dateDays_992_, v___y_991_);
lean_dec(v___y_991_);
lean_dec(v_dateDays_992_);
v___x_994_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_993_);
lean_dec(v___x_993_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object* v_date_1004_, lean_object* v_desiredWeekday_1005_){
_start:
{
uint8_t v_desiredWeekday_boxed_1006_; lean_object* v_res_1007_; 
v_desiredWeekday_boxed_1006_ = lean_unbox(v_desiredWeekday_1005_);
v_res_1007_ = l_Std_Time_PlainDate_withWeekday(v_date_1004_, v_desiredWeekday_boxed_1006_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object* v_date_1008_){
_start:
{
lean_object* v_year_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_w_1019_; uint8_t v___x_1020_; 
v_year_1009_ = lean_ctor_get(v_date_1008_, 0);
lean_inc(v_year_1009_);
v___x_1010_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1011_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1012_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11);
v___x_1013_ = l_Std_Time_PlainDate_dayOfYear(v_date_1008_);
v___x_1014_ = lean_int_add(v___x_1012_, v___x_1013_);
lean_dec(v___x_1013_);
v___x_1015_ = l_Std_Time_PlainDate_weekday(v_date_1008_);
v___x_1016_ = l_Std_Time_Weekday_toOrdinal(v___x_1015_);
v___x_1017_ = lean_int_neg(v___x_1016_);
lean_dec(v___x_1016_);
v___x_1018_ = lean_int_add(v___x_1014_, v___x_1017_);
lean_dec(v___x_1017_);
lean_dec(v___x_1014_);
v_w_1019_ = lean_int_ediv(v___x_1018_, v___x_1011_);
lean_dec(v___x_1018_);
v___x_1020_ = lean_int_dec_lt(v_w_1019_, v___x_1010_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = l_Std_Time_Year_Offset_weeks(v_year_1009_);
lean_dec(v_year_1009_);
v___x_1022_ = lean_int_dec_lt(v___x_1021_, v_w_1019_);
lean_dec(v___x_1021_);
if (v___x_1022_ == 0)
{
return v_w_1019_;
}
else
{
lean_dec(v_w_1019_);
return v___x_1010_;
}
}
else
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec(v_w_1019_);
v___x_1023_ = lean_int_sub(v_year_1009_, v___x_1010_);
lean_dec(v_year_1009_);
v___x_1024_ = l_Std_Time_Year_Offset_weeks(v___x_1023_);
lean_dec(v___x_1023_);
return v___x_1024_;
}
}
}
lean_object* runtime_initialize_Std_Time_Date_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Year(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_PlainDate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Date_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Year(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedPlainDate = _init_l_Std_Time_instInhabitedPlainDate();
lean_mark_persistent(l_Std_Time_instInhabitedPlainDate);
l_Std_Time_PlainDate_instInhabited = _init_l_Std_Time_PlainDate_instInhabited();
lean_mark_persistent(l_Std_Time_PlainDate_instInhabited);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_PlainDate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Date_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Year(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_PlainDate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Year(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_PlainDate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Date_PlainDate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Date_PlainDate(builtin);
}
#ifdef __cplusplus
}
#endif
