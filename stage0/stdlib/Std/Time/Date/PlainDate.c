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
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_Day_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Month_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Year_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Std_Time_Day_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
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
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__2;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__3;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__4;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__5;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__6;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__7;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__8;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__9;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__10;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__11;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__12;
static lean_once_cell_t l_Std_Time_PlainDate_ofEpochDay___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_ofEpochDay___closed__13;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofEpochDay___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_toEpochDay___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_toEpochDay___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_toEpochDay___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_toEpochDay___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
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
static lean_once_cell_t l_Std_Time_PlainDate_weekOfMonth___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfMonth___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfMonth___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfMonth___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2;
static lean_once_cell_t l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3;
static lean_once_cell_t l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4;
static lean_once_cell_t l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5;
static lean_once_cell_t l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6;
static lean_once_cell_t l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__2;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__3;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__4;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__5;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__6;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__7;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__8;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__9;
static lean_once_cell_t l_Std_Time_PlainDate_weekOfYear___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_weekOfYear___closed__10;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekYear___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_year_47_; lean_object* v_month_48_; lean_object* v_day_49_; lean_object* v___x_50_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; lean_object* v___y_55_; uint8_t v___y_56_; lean_object* v___y_57_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___y_89_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
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
lean_inc(v___y_54_);
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___y_54_);
lean_ctor_set(v___x_58_, 1, v___y_57_);
v___x_59_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v___y_56_);
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___y_53_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
lean_inc_n(v___y_55_, 2);
v___x_61_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___y_55_);
lean_inc_n(v___y_52_, 2);
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___y_52_);
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
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___y_56_);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_65_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___y_55_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___y_52_);
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
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___y_56_);
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
v___y_52_ = v___x_96_;
v___y_53_ = v___x_100_;
v___y_54_ = v___x_101_;
v___y_55_ = v___x_94_;
v___y_56_ = v___x_91_;
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
v___y_52_ = v___x_96_;
v___y_53_ = v___x_100_;
v___y_54_ = v___x_101_;
v___y_55_ = v___x_94_;
v___y_56_ = v___x_91_;
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
v___x_241_ = lean_unsigned_to_nat(100u);
v___x_242_ = lean_nat_to_int(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(400u);
v___x_244_ = lean_nat_to_int(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip(lean_object* v_year_245_, lean_object* v_month_246_, lean_object* v_day_247_){
_start:
{
uint8_t v___y_249_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; uint8_t v___y_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_254_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_255_ = lean_int_mod(v_year_245_, v___x_254_);
v___x_256_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_257_ = lean_int_dec_eq(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
v___x_260_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_261_ = lean_int_mod(v_year_245_, v___x_260_);
v___x_262_ = lean_int_dec_eq(v___x_261_, v___x_256_);
lean_dec(v___x_261_);
if (v___x_262_ == 0)
{
uint8_t v___x_263_; 
v___x_263_ = 1;
v___y_259_ = v___x_263_;
goto v___jp_258_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_265_ = lean_int_mod(v_year_245_, v___x_264_);
v___x_266_ = lean_int_dec_eq(v___x_265_, v___x_256_);
lean_dec(v___x_265_);
v___y_259_ = v___x_266_;
goto v___jp_258_;
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
v___jp_258_:
{
if (v___x_257_ == 0)
{
v___y_249_ = v___x_257_;
goto v___jp_248_;
}
else
{
v___y_249_ = v___y_259_;
goto v___jp_248_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__17, &l_Std_Time_instInhabitedPlainDate___closed__17_once, _init_l_Std_Time_instInhabitedPlainDate___closed__17);
v___x_268_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__9, &l_Std_Time_instInhabitedPlainDate___closed__9_once, _init_l_Std_Time_instInhabitedPlainDate___closed__9);
v___x_269_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_268_);
lean_ctor_set(v___x_270_, 2, v___x_267_);
return v___x_270_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited(void){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Std_Time_PlainDate_instInhabited___closed__0, &l_Std_Time_PlainDate_instInhabited___closed__0_once, _init_l_Std_Time_PlainDate_instInhabited___closed__0);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDay_x3f(lean_object* v_year_272_, lean_object* v_month_273_, lean_object* v_day_274_){
_start:
{
uint8_t v___y_276_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; uint8_t v___y_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_282_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_283_ = lean_int_mod(v_year_272_, v___x_282_);
v___x_284_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_285_ = lean_int_dec_eq(v___x_283_, v___x_284_);
lean_dec(v___x_283_);
v___x_288_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_289_ = lean_int_mod(v_year_272_, v___x_288_);
v___x_290_ = lean_int_dec_eq(v___x_289_, v___x_284_);
lean_dec(v___x_289_);
if (v___x_290_ == 0)
{
uint8_t v___x_291_; 
v___x_291_ = 1;
v___y_287_ = v___x_291_;
goto v___jp_286_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_293_ = lean_int_mod(v_year_272_, v___x_292_);
v___x_294_ = lean_int_dec_eq(v___x_293_, v___x_284_);
lean_dec(v___x_293_);
v___y_287_ = v___x_294_;
goto v___jp_286_;
}
v___jp_275_:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = l_Std_Time_Month_Ordinal_days(v___y_276_, v_month_273_);
v___x_278_ = lean_int_dec_le(v_day_274_, v___x_277_);
lean_dec(v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec(v_day_274_);
lean_dec(v_month_273_);
lean_dec(v_year_272_);
v___x_279_ = lean_box(0);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_280_, 0, v_year_272_);
lean_ctor_set(v___x_280_, 1, v_month_273_);
lean_ctor_set(v___x_280_, 2, v_day_274_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
v___jp_286_:
{
if (v___x_285_ == 0)
{
v___y_276_ = v___x_285_;
goto v___jp_275_;
}
else
{
v___y_276_ = v___y_287_;
goto v___jp_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal(lean_object* v_year_295_, lean_object* v_ordinal_296_){
_start:
{
uint8_t v___y_298_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; uint8_t v___y_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_303_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_304_ = lean_int_mod(v_year_295_, v___x_303_);
v___x_305_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_306_ = lean_int_dec_eq(v___x_304_, v___x_305_);
lean_dec(v___x_304_);
v___x_309_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_310_ = lean_int_mod(v_year_295_, v___x_309_);
v___x_311_ = lean_int_dec_eq(v___x_310_, v___x_305_);
lean_dec(v___x_310_);
if (v___x_311_ == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 1;
v___y_308_ = v___x_312_;
goto v___jp_307_;
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_314_ = lean_int_mod(v_year_295_, v___x_313_);
v___x_315_ = lean_int_dec_eq(v___x_314_, v___x_305_);
lean_dec(v___x_314_);
v___y_308_ = v___x_315_;
goto v___jp_307_;
}
v___jp_297_:
{
lean_object* v_val_299_; lean_object* v_fst_300_; lean_object* v_snd_301_; lean_object* v___x_302_; 
v_val_299_ = l_Std_Time_ValidDate_ofOrdinal(v___y_298_, v_ordinal_296_);
v_fst_300_ = lean_ctor_get(v_val_299_, 0);
lean_inc(v_fst_300_);
v_snd_301_ = lean_ctor_get(v_val_299_, 1);
lean_inc(v_snd_301_);
lean_dec_ref(v_val_299_);
v___x_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_302_, 0, v_year_295_);
lean_ctor_set(v___x_302_, 1, v_fst_300_);
lean_ctor_set(v___x_302_, 2, v_snd_301_);
return v___x_302_;
}
v___jp_307_:
{
if (v___x_306_ == 0)
{
v___y_298_ = v___x_306_;
goto v___jp_297_;
}
else
{
v___y_298_ = v___y_308_;
goto v___jp_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal___boxed(lean_object* v_year_316_, lean_object* v_ordinal_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_Time_PlainDate_ofYearOrdinal(v_year_316_, v_ordinal_317_);
lean_dec(v_ordinal_317_);
return v_res_318_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__0(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(719468u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__1(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(31u);
v___x_322_ = lean_nat_to_int(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(12u);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__3(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(146097u);
v___x_326_ = lean_nat_to_int(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__4(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(1460u);
v___x_328_ = lean_nat_to_int(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__5(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(36524u);
v___x_330_ = lean_nat_to_int(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__6(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(146096u);
v___x_332_ = lean_nat_to_int(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__7(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(365u);
v___x_334_ = lean_nat_to_int(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__8(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(5u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__9(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__10(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(153u);
v___x_340_ = lean_nat_to_int(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__11(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(10u);
v___x_342_ = lean_nat_to_int(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__12(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___x_344_ = lean_int_neg(v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__13(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(3u);
v___x_346_ = lean_nat_to_int(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object* v_day_347_){
_start:
{
lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___y_352_; uint8_t v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; uint8_t v___y_362_; lean_object* v___x_363_; lean_object* v_z_364_; lean_object* v___x_365_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_408_; lean_object* v___y_409_; lean_object* v___y_410_; lean_object* v___y_411_; lean_object* v___y_412_; lean_object* v___y_413_; lean_object* v___y_417_; uint8_t v___x_460_; 
v___x_363_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__0, &l_Std_Time_PlainDate_ofEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__0);
v_z_364_ = lean_int_add(v_day_347_, v___x_363_);
v___x_365_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_460_ = lean_int_dec_le(v___x_365_, v_z_364_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__6, &l_Std_Time_PlainDate_ofEpochDay___closed__6_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__6);
v___x_462_ = lean_int_sub(v_z_364_, v___x_461_);
v___y_417_ = v___x_462_;
goto v___jp_416_;
}
else
{
lean_inc(v_z_364_);
v___y_417_ = v_z_364_;
goto v___jp_416_;
}
v___jp_348_:
{
lean_object* v_max_353_; uint8_t v___x_354_; 
v_max_353_ = l_Std_Time_Month_Ordinal_days(v___y_352_, v___y_351_);
v___x_354_ = lean_int_dec_lt(v_max_353_, v___y_349_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_dec(v_max_353_);
v___x_355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_355_, 0, v___y_350_);
lean_ctor_set(v___x_355_, 1, v___y_351_);
lean_ctor_set(v___x_355_, 2, v___y_349_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; 
lean_dec(v___y_349_);
v___x_356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_356_, 0, v___y_350_);
lean_ctor_set(v___x_356_, 1, v___y_351_);
lean_ctor_set(v___x_356_, 2, v_max_353_);
return v___x_356_;
}
}
v___jp_357_:
{
if (v___y_358_ == 0)
{
v___y_349_ = v___y_359_;
v___y_350_ = v___y_360_;
v___y_351_ = v___y_361_;
v___y_352_ = v___y_358_;
goto v___jp_348_;
}
else
{
v___y_349_ = v___y_359_;
v___y_350_ = v___y_360_;
v___y_351_ = v___y_361_;
v___y_352_ = v___y_362_;
goto v___jp_348_;
}
}
v___jp_366_:
{
lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_373_ = lean_int_mod(v___y_369_, v___y_368_);
v___x_374_ = lean_int_dec_eq(v___x_373_, v___x_365_);
lean_dec(v___x_373_);
v___x_375_ = lean_int_mod(v___y_369_, v___y_370_);
v___x_376_ = lean_int_dec_eq(v___x_375_, v___x_365_);
lean_dec(v___x_375_);
if (v___x_376_ == 0)
{
uint8_t v___x_377_; 
v___x_377_ = 1;
v___y_358_ = v___x_374_;
v___y_359_ = v___y_372_;
v___y_360_ = v___y_369_;
v___y_361_ = v___y_371_;
v___y_362_ = v___x_377_;
goto v___jp_357_;
}
else
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_int_mod(v___y_369_, v___y_367_);
v___x_379_ = lean_int_dec_eq(v___x_378_, v___x_365_);
lean_dec(v___x_378_);
v___y_358_ = v___x_374_;
v___y_359_ = v___y_372_;
v___y_360_ = v___y_369_;
v___y_361_ = v___y_371_;
v___y_362_ = v___x_379_;
goto v___jp_357_;
}
}
v___jp_380_:
{
uint8_t v___x_388_; 
v___x_388_ = lean_int_dec_le(v___y_382_, v___y_386_);
if (v___x_388_ == 0)
{
lean_dec(v___y_386_);
lean_inc(v___y_382_);
v___y_367_ = v___y_381_;
v___y_368_ = v___y_384_;
v___y_369_ = v___y_383_;
v___y_370_ = v___y_385_;
v___y_371_ = v___y_387_;
v___y_372_ = v___y_382_;
goto v___jp_366_;
}
else
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__1, &l_Std_Time_PlainDate_ofEpochDay___closed__1_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__1);
v___x_390_ = lean_int_dec_le(v___y_386_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v___y_386_);
v___y_367_ = v___y_381_;
v___y_368_ = v___y_384_;
v___y_369_ = v___y_383_;
v___y_370_ = v___y_385_;
v___y_371_ = v___y_387_;
v___y_372_ = v___x_389_;
goto v___jp_366_;
}
else
{
v___y_367_ = v___y_381_;
v___y_368_ = v___y_384_;
v___y_369_ = v___y_383_;
v___y_370_ = v___y_385_;
v___y_371_ = v___y_387_;
v___y_372_ = v___y_386_;
goto v___jp_366_;
}
}
}
v___jp_391_:
{
lean_object* v_y_400_; uint8_t v___x_401_; 
v_y_400_ = lean_int_add(v___y_392_, v___y_399_);
lean_dec(v___y_392_);
v___x_401_ = lean_int_dec_le(v___y_394_, v___y_398_);
if (v___x_401_ == 0)
{
lean_dec(v___y_398_);
lean_inc(v___y_394_);
v___y_381_ = v___y_393_;
v___y_382_ = v___y_394_;
v___y_383_ = v_y_400_;
v___y_384_ = v___y_395_;
v___y_385_ = v___y_396_;
v___y_386_ = v___y_397_;
v___y_387_ = v___y_394_;
goto v___jp_380_;
}
else
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_403_ = lean_int_dec_le(v___y_398_, v___x_402_);
if (v___x_403_ == 0)
{
lean_dec(v___y_398_);
v___y_381_ = v___y_393_;
v___y_382_ = v___y_394_;
v___y_383_ = v_y_400_;
v___y_384_ = v___y_395_;
v___y_385_ = v___y_396_;
v___y_386_ = v___y_397_;
v___y_387_ = v___x_402_;
goto v___jp_380_;
}
else
{
v___y_381_ = v___y_393_;
v___y_382_ = v___y_394_;
v___y_383_ = v_y_400_;
v___y_384_ = v___y_395_;
v___y_385_ = v___y_396_;
v___y_386_ = v___y_397_;
v___y_387_ = v___y_398_;
goto v___jp_380_;
}
}
}
v___jp_404_:
{
lean_object* v_m_414_; uint8_t v___x_415_; 
v_m_414_ = lean_int_add(v___y_412_, v___y_413_);
lean_dec(v___y_412_);
v___x_415_ = lean_int_dec_le(v_m_414_, v___y_411_);
if (v___x_415_ == 0)
{
v___y_392_ = v___y_405_;
v___y_393_ = v___y_406_;
v___y_394_ = v___y_407_;
v___y_395_ = v___y_408_;
v___y_396_ = v___y_409_;
v___y_397_ = v___y_410_;
v___y_398_ = v_m_414_;
v___y_399_ = v___x_365_;
goto v___jp_391_;
}
else
{
v___y_392_ = v___y_405_;
v___y_393_ = v___y_406_;
v___y_394_ = v___y_407_;
v___y_395_ = v___y_408_;
v___y_396_ = v___y_409_;
v___y_397_ = v___y_410_;
v___y_398_ = v_m_414_;
v___y_399_ = v___y_407_;
goto v___jp_391_;
}
}
v___jp_416_:
{
lean_object* v___x_418_; lean_object* v_era_419_; lean_object* v___x_420_; lean_object* v_doe_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v_yoe_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_y_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_doy_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_mp_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_d_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_418_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__3, &l_Std_Time_PlainDate_ofEpochDay___closed__3_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__3);
v_era_419_ = lean_int_div(v___y_417_, v___x_418_);
lean_dec(v___y_417_);
v___x_420_ = lean_int_mul(v_era_419_, v___x_418_);
v_doe_421_ = lean_int_sub(v_z_364_, v___x_420_);
lean_dec(v___x_420_);
lean_dec(v_z_364_);
v___x_422_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__4, &l_Std_Time_PlainDate_ofEpochDay___closed__4_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__4);
v___x_423_ = lean_int_div(v_doe_421_, v___x_422_);
v___x_424_ = lean_int_sub(v_doe_421_, v___x_423_);
lean_dec(v___x_423_);
v___x_425_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__5, &l_Std_Time_PlainDate_ofEpochDay___closed__5_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__5);
v___x_426_ = lean_int_div(v_doe_421_, v___x_425_);
v___x_427_ = lean_int_add(v___x_424_, v___x_426_);
lean_dec(v___x_426_);
lean_dec(v___x_424_);
v___x_428_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__6, &l_Std_Time_PlainDate_ofEpochDay___closed__6_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__6);
v___x_429_ = lean_int_div(v_doe_421_, v___x_428_);
v___x_430_ = lean_int_sub(v___x_427_, v___x_429_);
lean_dec(v___x_429_);
lean_dec(v___x_427_);
v___x_431_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__7, &l_Std_Time_PlainDate_ofEpochDay___closed__7_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__7);
v_yoe_432_ = lean_int_div(v___x_430_, v___x_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_434_ = lean_int_mul(v_era_419_, v___x_433_);
lean_dec(v_era_419_);
v_y_435_ = lean_int_add(v_yoe_432_, v___x_434_);
lean_dec(v___x_434_);
v___x_436_ = lean_int_mul(v___x_431_, v_yoe_432_);
v___x_437_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_438_ = lean_int_div(v_yoe_432_, v___x_437_);
v___x_439_ = lean_int_add(v___x_436_, v___x_438_);
lean_dec(v___x_438_);
lean_dec(v___x_436_);
v___x_440_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_441_ = lean_int_div(v_yoe_432_, v___x_440_);
lean_dec(v_yoe_432_);
v___x_442_ = lean_int_sub(v___x_439_, v___x_441_);
lean_dec(v___x_441_);
lean_dec(v___x_439_);
v_doy_443_ = lean_int_sub(v_doe_421_, v___x_442_);
lean_dec(v___x_442_);
lean_dec(v_doe_421_);
v___x_444_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_445_ = lean_int_mul(v___x_444_, v_doy_443_);
v___x_446_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__9, &l_Std_Time_PlainDate_ofEpochDay___closed__9_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__9);
v___x_447_ = lean_int_add(v___x_445_, v___x_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__10, &l_Std_Time_PlainDate_ofEpochDay___closed__10_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__10);
v_mp_449_ = lean_int_div(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_int_mul(v___x_448_, v_mp_449_);
v___x_451_ = lean_int_add(v___x_450_, v___x_446_);
lean_dec(v___x_450_);
v___x_452_ = lean_int_div(v___x_451_, v___x_444_);
lean_dec(v___x_451_);
v___x_453_ = lean_int_sub(v_doy_443_, v___x_452_);
lean_dec(v___x_452_);
lean_dec(v_doy_443_);
v___x_454_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_d_455_ = lean_int_add(v___x_453_, v___x_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__11, &l_Std_Time_PlainDate_ofEpochDay___closed__11_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__11);
v___x_457_ = lean_int_dec_lt(v_mp_449_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__12, &l_Std_Time_PlainDate_ofEpochDay___closed__12_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__12);
v___y_405_ = v_y_435_;
v___y_406_ = v___x_433_;
v___y_407_ = v___x_454_;
v___y_408_ = v___x_437_;
v___y_409_ = v___x_440_;
v___y_410_ = v_d_455_;
v___y_411_ = v___x_446_;
v___y_412_ = v_mp_449_;
v___y_413_ = v___x_458_;
goto v___jp_404_;
}
else
{
lean_object* v___x_459_; 
v___x_459_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___y_405_ = v_y_435_;
v___y_406_ = v___x_433_;
v___y_407_ = v___x_454_;
v___y_408_ = v___x_437_;
v___y_409_ = v___x_440_;
v___y_410_ = v_d_455_;
v___y_411_ = v___x_446_;
v___y_412_ = v_mp_449_;
v___y_413_ = v___x_459_;
goto v___jp_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofEpochDay___boxed(lean_object* v_day_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Time_PlainDate_ofEpochDay(v_day_463_);
lean_dec(v_day_463_);
return v_res_464_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_466_ = lean_int_neg(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object* v_date_467_){
_start:
{
lean_object* v_day_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_day_468_ = lean_ctor_get(v_date_467_, 2);
v___x_469_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_470_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_471_ = lean_obj_once(&l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0, &l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0);
v___x_472_ = lean_int_add(v_day_468_, v___x_471_);
v___x_473_ = lean_int_ediv(v___x_472_, v___x_470_);
lean_dec(v___x_472_);
v___x_474_ = lean_int_add(v___x_473_, v___x_469_);
lean_dec(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth___boxed(lean_object* v_date_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_475_);
lean_dec_ref(v_date_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object* v_date_477_){
_start:
{
lean_object* v_month_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_month_478_ = lean_ctor_get(v_date_477_, 1);
v___x_479_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_480_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___x_481_ = lean_obj_once(&l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0, &l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0);
v___x_482_ = lean_int_add(v_month_478_, v___x_481_);
v___x_483_ = lean_int_ediv(v___x_482_, v___x_480_);
lean_dec(v___x_482_);
v___x_484_ = lean_int_add(v___x_483_, v___x_479_);
lean_dec(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object* v_date_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Time_PlainDate_quarter(v_date_485_);
lean_dec_ref(v_date_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object* v_date_487_){
_start:
{
lean_object* v_year_488_; lean_object* v_month_489_; lean_object* v_day_490_; uint8_t v___y_492_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; uint8_t v___y_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_year_488_ = lean_ctor_get(v_date_487_, 0);
v_month_489_ = lean_ctor_get(v_date_487_, 1);
v_day_490_ = lean_ctor_get(v_date_487_, 2);
v___x_495_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_496_ = lean_int_mod(v_year_488_, v___x_495_);
v___x_497_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_498_ = lean_int_dec_eq(v___x_496_, v___x_497_);
lean_dec(v___x_496_);
v___x_501_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_502_ = lean_int_mod(v_year_488_, v___x_501_);
v___x_503_ = lean_int_dec_eq(v___x_502_, v___x_497_);
lean_dec(v___x_502_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = 1;
v___y_500_ = v___x_504_;
goto v___jp_499_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_505_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_506_ = lean_int_mod(v_year_488_, v___x_505_);
v___x_507_ = lean_int_dec_eq(v___x_506_, v___x_497_);
lean_dec(v___x_506_);
v___y_500_ = v___x_507_;
goto v___jp_499_;
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc(v_day_490_);
lean_inc(v_month_489_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_month_489_);
lean_ctor_set(v___x_493_, 1, v_day_490_);
v___x_494_ = l_Std_Time_ValidDate_dayOfYear(v___y_492_, v___x_493_);
lean_dec_ref_known(v___x_493_, 2);
return v___x_494_;
}
v___jp_499_:
{
if (v___x_498_ == 0)
{
v___y_492_ = v___x_498_;
goto v___jp_491_;
}
else
{
v___y_492_ = v___y_500_;
goto v___jp_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object* v_date_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Time_PlainDate_dayOfYear(v_date_508_);
lean_dec_ref(v_date_508_);
return v_res_509_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_era(lean_object* v_date_510_){
_start:
{
lean_object* v_year_511_; uint8_t v___x_512_; 
v_year_511_ = lean_ctor_get(v_date_510_, 0);
v___x_512_ = l_Std_Time_Year_Offset_era(v_year_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object* v_date_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_Std_Time_PlainDate_era(v_date_513_);
lean_dec_ref(v_date_513_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object* v_date_516_){
_start:
{
lean_object* v_year_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_year_517_ = lean_ctor_get(v_date_516_, 0);
v___x_518_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_519_ = lean_int_mod(v_year_517_, v___x_518_);
v___x_520_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_521_ = lean_int_dec_eq(v___x_519_, v___x_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_523_ = lean_int_mod(v_year_517_, v___x_522_);
v___x_524_ = lean_int_dec_eq(v___x_523_, v___x_520_);
lean_dec(v___x_523_);
if (v___x_524_ == 0)
{
return v___x_521_;
}
else
{
if (v___x_521_ == 0)
{
return v___x_521_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_526_ = lean_int_mod(v_year_517_, v___x_525_);
v___x_527_ = lean_int_dec_eq(v___x_526_, v___x_520_);
lean_dec(v___x_526_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object* v_date_528_){
_start:
{
uint8_t v_res_529_; lean_object* v_r_530_; 
v_res_529_ = l_Std_Time_PlainDate_inLeapYear(v_date_528_);
lean_dec_ref(v_date_528_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toEpochDay___closed__0(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___x_532_ = lean_int_neg(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toEpochDay___closed__1(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(399u);
v___x_534_ = lean_nat_to_int(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object* v_date_535_){
_start:
{
lean_object* v_year_536_; lean_object* v_month_537_; lean_object* v_day_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_579_; uint8_t v___x_584_; 
v_year_536_ = lean_ctor_get(v_date_535_, 0);
lean_inc(v_year_536_);
v_month_537_ = lean_ctor_get(v_date_535_, 1);
lean_inc(v_month_537_);
v_day_538_ = lean_ctor_get(v_date_535_, 2);
lean_inc(v_day_538_);
lean_dec_ref(v_date_535_);
v___x_539_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__9, &l_Std_Time_PlainDate_ofEpochDay___closed__9_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__9);
v___x_540_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_584_ = lean_int_dec_lt(v___x_539_, v_month_537_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
v___x_585_ = lean_int_sub(v_year_536_, v___x_540_);
lean_dec(v_year_536_);
v___y_579_ = v___x_585_;
goto v___jp_578_;
}
else
{
v___y_579_ = v_year_536_;
goto v___jp_578_;
}
v___jp_541_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_doy_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_doe_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_546_ = lean_int_add(v_month_537_, v___y_545_);
lean_dec(v_month_537_);
v___x_547_ = lean_int_mul(v___y_542_, v___x_546_);
lean_dec(v___x_546_);
v___x_548_ = lean_int_add(v___x_547_, v___x_539_);
lean_dec(v___x_547_);
v___x_549_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_550_ = lean_int_div(v___x_548_, v___x_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_int_add(v___x_550_, v_day_538_);
lean_dec(v_day_538_);
lean_dec(v___x_550_);
v_doy_552_ = lean_int_sub(v___x_551_, v___x_540_);
lean_dec(v___x_551_);
v___x_553_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__7, &l_Std_Time_PlainDate_ofEpochDay___closed__7_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__7);
v___x_554_ = lean_int_mul(v___y_544_, v___x_553_);
v___x_555_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_556_ = lean_int_div(v___y_544_, v___x_555_);
v___x_557_ = lean_int_add(v___x_554_, v___x_556_);
lean_dec(v___x_556_);
lean_dec(v___x_554_);
v___x_558_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_559_ = lean_int_div(v___y_544_, v___x_558_);
lean_dec(v___y_544_);
v___x_560_ = lean_int_sub(v___x_557_, v___x_559_);
lean_dec(v___x_559_);
lean_dec(v___x_557_);
v_doe_561_ = lean_int_add(v___x_560_, v_doy_552_);
lean_dec(v_doy_552_);
lean_dec(v___x_560_);
v___x_562_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__3, &l_Std_Time_PlainDate_ofEpochDay___closed__3_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__3);
v___x_563_ = lean_int_mul(v___y_543_, v___x_562_);
lean_dec(v___y_543_);
v___x_564_ = lean_int_add(v___x_563_, v_doe_561_);
lean_dec(v_doe_561_);
lean_dec(v___x_563_);
v___x_565_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__0, &l_Std_Time_PlainDate_ofEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__0);
v___x_566_ = lean_int_sub(v___x_564_, v___x_565_);
lean_dec(v___x_564_);
return v___x_566_;
}
v___jp_567_:
{
lean_object* v___x_570_; lean_object* v_era_571_; lean_object* v___x_572_; lean_object* v_yoe_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_570_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v_era_571_ = lean_int_div(v___y_569_, v___x_570_);
lean_dec(v___y_569_);
v___x_572_ = lean_int_mul(v_era_571_, v___x_570_);
v_yoe_573_ = lean_int_sub(v___y_568_, v___x_572_);
lean_dec(v___x_572_);
lean_dec(v___y_568_);
v___x_574_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__10, &l_Std_Time_PlainDate_ofEpochDay___closed__10_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__10);
v___x_575_ = lean_int_dec_lt(v___x_539_, v_month_537_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___y_542_ = v___x_574_;
v___y_543_ = v_era_571_;
v___y_544_ = v_yoe_573_;
v___y_545_ = v___x_576_;
goto v___jp_541_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Std_Time_PlainDate_toEpochDay___closed__0, &l_Std_Time_PlainDate_toEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_toEpochDay___closed__0);
v___y_542_ = v___x_574_;
v___y_543_ = v_era_571_;
v___y_544_ = v_yoe_573_;
v___y_545_ = v___x_577_;
goto v___jp_541_;
}
}
v___jp_578_:
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_581_ = lean_int_dec_le(v___x_580_, v___y_579_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_obj_once(&l_Std_Time_PlainDate_toEpochDay___closed__1, &l_Std_Time_PlainDate_toEpochDay___closed__1_once, _init_l_Std_Time_PlainDate_toEpochDay___closed__1);
v___x_583_ = lean_int_sub(v___y_579_, v___x_582_);
v___y_568_ = v___y_579_;
v___y_569_ = v___x_583_;
goto v___jp_567_;
}
else
{
lean_inc(v___y_579_);
v___y_568_ = v___y_579_;
v___y_569_ = v___y_579_;
goto v___jp_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays(lean_object* v_date_586_, lean_object* v_days_587_){
_start:
{
lean_object* v_dateDays_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_dateDays_588_ = l_Std_Time_PlainDate_toEpochDay(v_date_586_);
v___x_589_ = lean_int_add(v_dateDays_588_, v_days_587_);
lean_dec(v_dateDays_588_);
v___x_590_ = l_Std_Time_PlainDate_ofEpochDay(v___x_589_);
lean_dec(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays___boxed(lean_object* v_date_591_, lean_object* v_days_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_Time_PlainDate_addDays(v_date_591_, v_days_592_);
lean_dec(v_days_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays(lean_object* v_date_594_, lean_object* v_days_595_){
_start:
{
lean_object* v___x_596_; lean_object* v_dateDays_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_596_ = lean_int_neg(v_days_595_);
v_dateDays_597_ = l_Std_Time_PlainDate_toEpochDay(v_date_594_);
v___x_598_ = lean_int_add(v_dateDays_597_, v___x_596_);
lean_dec(v___x_596_);
lean_dec(v_dateDays_597_);
v___x_599_ = l_Std_Time_PlainDate_ofEpochDay(v___x_598_);
lean_dec(v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays___boxed(lean_object* v_date_600_, lean_object* v_days_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_Time_PlainDate_subDays(v_date_600_, v_days_601_);
lean_dec(v_days_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks(lean_object* v_date_603_, lean_object* v_weeks_604_){
_start:
{
lean_object* v_dateDays_605_; lean_object* v___x_606_; lean_object* v_daysToAdd_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_dateDays_605_ = l_Std_Time_PlainDate_toEpochDay(v_date_603_);
v___x_606_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_607_ = lean_int_mul(v_weeks_604_, v___x_606_);
v___x_608_ = lean_int_add(v_dateDays_605_, v_daysToAdd_607_);
lean_dec(v_daysToAdd_607_);
lean_dec(v_dateDays_605_);
v___x_609_ = l_Std_Time_PlainDate_ofEpochDay(v___x_608_);
lean_dec(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks___boxed(lean_object* v_date_610_, lean_object* v_weeks_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_Time_PlainDate_addWeeks(v_date_610_, v_weeks_611_);
lean_dec(v_weeks_611_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks(lean_object* v_date_613_, lean_object* v_weeks_614_){
_start:
{
lean_object* v___x_615_; lean_object* v_dateDays_616_; lean_object* v___x_617_; lean_object* v_daysToAdd_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_615_ = lean_int_neg(v_weeks_614_);
v_dateDays_616_ = l_Std_Time_PlainDate_toEpochDay(v_date_613_);
v___x_617_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_618_ = lean_int_mul(v___x_615_, v___x_617_);
lean_dec(v___x_615_);
v___x_619_ = lean_int_add(v_dateDays_616_, v_daysToAdd_618_);
lean_dec(v_daysToAdd_618_);
lean_dec(v_dateDays_616_);
v___x_620_ = l_Std_Time_PlainDate_ofEpochDay(v___x_619_);
lean_dec(v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks___boxed(lean_object* v_date_621_, lean_object* v_weeks_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Std_Time_PlainDate_subWeeks(v_date_621_, v_weeks_622_);
lean_dec(v_weeks_622_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object* v_date_624_, lean_object* v_months_625_){
_start:
{
lean_object* v_year_626_; lean_object* v_month_627_; lean_object* v_day_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_663_; 
v_year_626_ = lean_ctor_get(v_date_624_, 0);
v_month_627_ = lean_ctor_get(v_date_624_, 1);
v_day_628_ = lean_ctor_get(v_date_624_, 2);
v_isSharedCheck_663_ = !lean_is_exclusive(v_date_624_);
if (v_isSharedCheck_663_ == 0)
{
v___x_630_ = v_date_624_;
v_isShared_631_ = v_isSharedCheck_663_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_day_628_);
lean_inc(v_month_627_);
lean_inc(v_year_626_);
lean_dec(v_date_624_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_663_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_totalMonths_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_wrappedMonths_637_; lean_object* v_yearsOffset_638_; lean_object* v___x_639_; uint8_t v___y_641_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; uint8_t v___y_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_632_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_633_ = lean_int_sub(v_month_627_, v___x_632_);
lean_dec(v_month_627_);
v_totalMonths_634_ = lean_int_add(v___x_633_, v_months_625_);
lean_dec(v___x_633_);
v___x_635_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_636_ = lean_int_emod(v_totalMonths_634_, v___x_635_);
v_wrappedMonths_637_ = lean_int_add(v___x_636_, v___x_632_);
lean_dec(v___x_636_);
v_yearsOffset_638_ = lean_int_ediv(v_totalMonths_634_, v___x_635_);
lean_dec(v_totalMonths_634_);
v___x_639_ = lean_int_add(v_year_626_, v_yearsOffset_638_);
lean_dec(v_yearsOffset_638_);
lean_dec(v_year_626_);
v___x_650_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_651_ = lean_int_mod(v___x_639_, v___x_650_);
v___x_652_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_653_ = lean_int_dec_eq(v___x_651_, v___x_652_);
lean_dec(v___x_651_);
v___x_656_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_657_ = lean_int_mod(v___x_639_, v___x_656_);
v___x_658_ = lean_int_dec_eq(v___x_657_, v___x_652_);
lean_dec(v___x_657_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
v___x_659_ = 1;
v___y_655_ = v___x_659_;
goto v___jp_654_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_661_ = lean_int_mod(v___x_639_, v___x_660_);
v___x_662_ = lean_int_dec_eq(v___x_661_, v___x_652_);
lean_dec(v___x_661_);
v___y_655_ = v___x_662_;
goto v___jp_654_;
}
v___jp_640_:
{
lean_object* v_max_642_; uint8_t v___x_643_; 
v_max_642_ = l_Std_Time_Month_Ordinal_days(v___y_641_, v_wrappedMonths_637_);
v___x_643_ = lean_int_dec_lt(v_max_642_, v_day_628_);
if (v___x_643_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v_max_642_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v_wrappedMonths_637_);
lean_ctor_set(v___x_630_, 0, v___x_639_);
v___x_645_ = v___x_630_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_wrappedMonths_637_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_day_628_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v_day_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 2, v_max_642_);
lean_ctor_set(v___x_630_, 1, v_wrappedMonths_637_);
lean_ctor_set(v___x_630_, 0, v___x_639_);
v___x_648_ = v___x_630_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_wrappedMonths_637_);
lean_ctor_set(v_reuseFailAlloc_649_, 2, v_max_642_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
v___jp_654_:
{
if (v___x_653_ == 0)
{
v___y_641_ = v___x_653_;
goto v___jp_640_;
}
else
{
v___y_641_ = v___y_655_;
goto v___jp_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip___boxed(lean_object* v_date_664_, lean_object* v_months_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_Time_PlainDate_addMonthsClip(v_date_664_, v_months_665_);
lean_dec(v_months_665_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip(lean_object* v_date_667_, lean_object* v_months_668_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_int_neg(v_months_668_);
v___x_670_ = l_Std_Time_PlainDate_addMonthsClip(v_date_667_, v___x_669_);
lean_dec(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip___boxed(lean_object* v_date_671_, lean_object* v_months_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Time_PlainDate_subMonthsClip(v_date_671_, v_months_672_);
lean_dec(v_months_672_);
return v_res_673_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__0(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(30u);
v___x_675_ = lean_nat_to_int(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__1(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__0, &l_Std_Time_PlainDate_rollOver___closed__0_once, _init_l_Std_Time_PlainDate_rollOver___closed__0);
v___x_677_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_678_ = lean_int_add(v___x_677_, v___x_676_);
return v___x_678_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__2(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_680_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__1, &l_Std_Time_PlainDate_rollOver___closed__1_once, _init_l_Std_Time_PlainDate_rollOver___closed__1);
v___x_681_ = lean_int_sub(v___x_680_, v___x_679_);
return v___x_681_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__3(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v_range_684_; 
v___x_682_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_683_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__2, &l_Std_Time_PlainDate_rollOver___closed__2_once, _init_l_Std_Time_PlainDate_rollOver___closed__2);
v_range_684_ = lean_int_add(v___x_683_, v___x_682_);
return v_range_684_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__4(void){
_start:
{
lean_object* v_range_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_range_685_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_686_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_687_ = lean_int_emod(v___x_686_, v_range_685_);
return v___x_687_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__5(void){
_start:
{
lean_object* v_range_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_range_688_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_689_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__4, &l_Std_Time_PlainDate_rollOver___closed__4_once, _init_l_Std_Time_PlainDate_rollOver___closed__4);
v___x_690_ = lean_int_add(v___x_689_, v_range_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__6(void){
_start:
{
lean_object* v_range_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_range_691_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_692_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__5, &l_Std_Time_PlainDate_rollOver___closed__5_once, _init_l_Std_Time_PlainDate_rollOver___closed__5);
v___x_693_ = lean_int_emod(v___x_692_, v_range_691_);
return v___x_693_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__7(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_695_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__6, &l_Std_Time_PlainDate_rollOver___closed__6_once, _init_l_Std_Time_PlainDate_rollOver___closed__6);
v___x_696_ = lean_int_add(v___x_695_, v___x_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver(lean_object* v_year_697_, lean_object* v_month_698_, lean_object* v_day_699_){
_start:
{
lean_object* v___y_701_; lean_object* v___x_707_; uint8_t v___y_709_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; uint8_t v___y_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_707_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_714_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_715_ = lean_int_mod(v_year_697_, v___x_714_);
v___x_716_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_717_ = lean_int_dec_eq(v___x_715_, v___x_716_);
lean_dec(v___x_715_);
v___x_720_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_721_ = lean_int_mod(v_year_697_, v___x_720_);
v___x_722_ = lean_int_dec_eq(v___x_721_, v___x_716_);
lean_dec(v___x_721_);
if (v___x_722_ == 0)
{
uint8_t v___x_723_; 
v___x_723_ = 1;
v___y_719_ = v___x_723_;
goto v___jp_718_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_724_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_725_ = lean_int_mod(v_year_697_, v___x_724_);
v___x_726_ = lean_int_dec_eq(v___x_725_, v___x_716_);
lean_dec(v___x_725_);
v___y_719_ = v___x_726_;
goto v___jp_718_;
}
v___jp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_dateDays_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_702_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_703_ = lean_int_sub(v_day_699_, v___x_702_);
v_dateDays_704_ = l_Std_Time_PlainDate_toEpochDay(v___y_701_);
v___x_705_ = lean_int_add(v_dateDays_704_, v___x_703_);
lean_dec(v___x_703_);
lean_dec(v_dateDays_704_);
v___x_706_ = l_Std_Time_PlainDate_ofEpochDay(v___x_705_);
lean_dec(v___x_705_);
return v___x_706_;
}
v___jp_708_:
{
lean_object* v_max_710_; uint8_t v___x_711_; 
v_max_710_ = l_Std_Time_Month_Ordinal_days(v___y_709_, v_month_698_);
v___x_711_ = lean_int_dec_lt(v_max_710_, v___x_707_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec(v_max_710_);
v___x_712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_712_, 0, v_year_697_);
lean_ctor_set(v___x_712_, 1, v_month_698_);
lean_ctor_set(v___x_712_, 2, v___x_707_);
v___y_701_ = v___x_712_;
goto v___jp_700_;
}
else
{
lean_object* v___x_713_; 
v___x_713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_713_, 0, v_year_697_);
lean_ctor_set(v___x_713_, 1, v_month_698_);
lean_ctor_set(v___x_713_, 2, v_max_710_);
v___y_701_ = v___x_713_;
goto v___jp_700_;
}
}
v___jp_718_:
{
if (v___x_717_ == 0)
{
v___y_709_ = v___x_717_;
goto v___jp_708_;
}
else
{
v___y_709_ = v___y_719_;
goto v___jp_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver___boxed(lean_object* v_year_727_, lean_object* v_month_728_, lean_object* v_day_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_Time_PlainDate_rollOver(v_year_727_, v_month_728_, v_day_729_);
lean_dec(v_day_729_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip(lean_object* v_dt_731_, lean_object* v_year_732_){
_start:
{
lean_object* v_month_733_; lean_object* v_day_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_761_; 
v_month_733_ = lean_ctor_get(v_dt_731_, 1);
v_day_734_ = lean_ctor_get(v_dt_731_, 2);
v_isSharedCheck_761_ = !lean_is_exclusive(v_dt_731_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v_dt_731_, 0);
lean_dec(v_unused_762_);
v___x_736_ = v_dt_731_;
v_isShared_737_ = v_isSharedCheck_761_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_day_734_);
lean_inc(v_month_733_);
lean_dec(v_dt_731_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_761_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___y_739_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; uint8_t v___y_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_748_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_749_ = lean_int_mod(v_year_732_, v___x_748_);
v___x_750_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_751_ = lean_int_dec_eq(v___x_749_, v___x_750_);
lean_dec(v___x_749_);
v___x_754_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_755_ = lean_int_mod(v_year_732_, v___x_754_);
v___x_756_ = lean_int_dec_eq(v___x_755_, v___x_750_);
lean_dec(v___x_755_);
if (v___x_756_ == 0)
{
uint8_t v___x_757_; 
v___x_757_ = 1;
v___y_753_ = v___x_757_;
goto v___jp_752_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_759_ = lean_int_mod(v_year_732_, v___x_758_);
v___x_760_ = lean_int_dec_eq(v___x_759_, v___x_750_);
lean_dec(v___x_759_);
v___y_753_ = v___x_760_;
goto v___jp_752_;
}
v___jp_738_:
{
lean_object* v_max_740_; uint8_t v___x_741_; 
v_max_740_ = l_Std_Time_Month_Ordinal_days(v___y_739_, v_month_733_);
v___x_741_ = lean_int_dec_lt(v_max_740_, v_day_734_);
if (v___x_741_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v_max_740_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v_year_732_);
v___x_743_ = v___x_736_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_year_732_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_month_733_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_day_734_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v___x_746_; 
lean_dec(v_day_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 2, v_max_740_);
lean_ctor_set(v___x_736_, 0, v_year_732_);
v___x_746_ = v___x_736_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_year_732_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_month_733_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v_max_740_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
v___jp_752_:
{
if (v___x_751_ == 0)
{
v___y_739_ = v___x_751_;
goto v___jp_738_;
}
else
{
v___y_739_ = v___y_753_;
goto v___jp_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearRollOver(lean_object* v_dt_763_, lean_object* v_year_764_){
_start:
{
lean_object* v_month_765_; lean_object* v_day_766_; lean_object* v___x_767_; 
v_month_765_ = lean_ctor_get(v_dt_763_, 1);
lean_inc(v_month_765_);
v_day_766_ = lean_ctor_get(v_dt_763_, 2);
lean_inc(v_day_766_);
lean_dec_ref(v_dt_763_);
v___x_767_ = l_Std_Time_PlainDate_rollOver(v_year_764_, v_month_765_, v_day_766_);
lean_dec(v_day_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object* v_date_768_, lean_object* v_months_769_){
_start:
{
lean_object* v_year_770_; lean_object* v_month_771_; lean_object* v_day_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_808_; 
v_year_770_ = lean_ctor_get(v_date_768_, 0);
v_month_771_ = lean_ctor_get(v_date_768_, 1);
v_day_772_ = lean_ctor_get(v_date_768_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_date_768_);
if (v_isSharedCheck_808_ == 0)
{
v___x_774_ = v_date_768_;
v_isShared_775_ = v_isSharedCheck_808_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_day_772_);
lean_inc(v_month_771_);
lean_inc(v_year_770_);
lean_dec(v_date_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_808_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___y_777_; lean_object* v___x_784_; uint8_t v___y_786_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; uint8_t v___y_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_784_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_795_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_796_ = lean_int_mod(v_year_770_, v___x_795_);
v___x_797_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_798_ = lean_int_dec_eq(v___x_796_, v___x_797_);
lean_dec(v___x_796_);
v___x_801_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_802_ = lean_int_mod(v_year_770_, v___x_801_);
v___x_803_ = lean_int_dec_eq(v___x_802_, v___x_797_);
lean_dec(v___x_802_);
if (v___x_803_ == 0)
{
uint8_t v___x_804_; 
v___x_804_ = 1;
v___y_800_ = v___x_804_;
goto v___jp_799_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_805_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_806_ = lean_int_mod(v_year_770_, v___x_805_);
v___x_807_ = lean_int_dec_eq(v___x_806_, v___x_797_);
lean_dec(v___x_806_);
v___y_800_ = v___x_807_;
goto v___jp_799_;
}
v___jp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_dateDays_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_778_ = l_Std_Time_PlainDate_addMonthsClip(v___y_777_, v_months_769_);
v___x_779_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_780_ = lean_int_sub(v_day_772_, v___x_779_);
lean_dec(v_day_772_);
v_dateDays_781_ = l_Std_Time_PlainDate_toEpochDay(v___x_778_);
v___x_782_ = lean_int_add(v_dateDays_781_, v___x_780_);
lean_dec(v___x_780_);
lean_dec(v_dateDays_781_);
v___x_783_ = l_Std_Time_PlainDate_ofEpochDay(v___x_782_);
lean_dec(v___x_782_);
return v___x_783_;
}
v___jp_785_:
{
lean_object* v_max_787_; uint8_t v___x_788_; 
v_max_787_ = l_Std_Time_Month_Ordinal_days(v___y_786_, v_month_771_);
v___x_788_ = lean_int_dec_lt(v_max_787_, v___x_784_);
if (v___x_788_ == 0)
{
lean_object* v___x_790_; 
lean_dec(v_max_787_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 2, v___x_784_);
v___x_790_ = v___x_774_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_year_770_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_month_771_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v___x_784_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v___y_777_ = v___x_790_;
goto v___jp_776_;
}
}
else
{
lean_object* v___x_793_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 2, v_max_787_);
v___x_793_ = v___x_774_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_year_770_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_month_771_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_max_787_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
v___y_777_ = v___x_793_;
goto v___jp_776_;
}
}
}
v___jp_799_:
{
if (v___x_798_ == 0)
{
v___y_786_ = v___x_798_;
goto v___jp_785_;
}
else
{
v___y_786_ = v___y_800_;
goto v___jp_785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver___boxed(lean_object* v_date_809_, lean_object* v_months_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_809_, v_months_810_);
lean_dec(v_months_810_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver(lean_object* v_date_812_, lean_object* v_months_813_){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_int_neg(v_months_813_);
v___x_815_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_812_, v___x_814_);
lean_dec(v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver___boxed(lean_object* v_date_816_, lean_object* v_months_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_Time_PlainDate_subMonthsRollOver(v_date_816_, v_months_817_);
lean_dec(v_months_817_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver(lean_object* v_date_819_, lean_object* v_years_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_822_ = lean_int_mul(v_years_820_, v___x_821_);
v___x_823_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_819_, v___x_822_);
lean_dec(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver___boxed(lean_object* v_date_824_, lean_object* v_years_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Time_PlainDate_addYearsRollOver(v_date_824_, v_years_825_);
lean_dec(v_years_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver(lean_object* v_date_827_, lean_object* v_years_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_830_ = lean_int_mul(v_years_828_, v___x_829_);
v___x_831_ = lean_int_neg(v___x_830_);
lean_dec(v___x_830_);
v___x_832_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_827_, v___x_831_);
lean_dec(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver___boxed(lean_object* v_date_833_, lean_object* v_years_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_Time_PlainDate_subYearsRollOver(v_date_833_, v_years_834_);
lean_dec(v_years_834_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip(lean_object* v_date_836_, lean_object* v_years_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_839_ = lean_int_mul(v_years_837_, v___x_838_);
v___x_840_ = l_Std_Time_PlainDate_addMonthsClip(v_date_836_, v___x_839_);
lean_dec(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip___boxed(lean_object* v_date_841_, lean_object* v_years_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Std_Time_PlainDate_addYearsClip(v_date_841_, v_years_842_);
lean_dec(v_years_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip(lean_object* v_date_844_, lean_object* v_years_845_){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_847_ = lean_int_mul(v_years_845_, v___x_846_);
v___x_848_ = lean_int_neg(v___x_847_);
lean_dec(v___x_847_);
v___x_849_ = l_Std_Time_PlainDate_addMonthsClip(v_date_844_, v___x_848_);
lean_dec(v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip___boxed(lean_object* v_date_850_, lean_object* v_years_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_Time_PlainDate_subYearsClip(v_date_850_, v_years_851_);
lean_dec(v_years_851_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip(lean_object* v_dt_853_, lean_object* v_days_854_){
_start:
{
lean_object* v_year_855_; lean_object* v_month_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_883_; 
v_year_855_ = lean_ctor_get(v_dt_853_, 0);
v_month_856_ = lean_ctor_get(v_dt_853_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_dt_853_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v_dt_853_, 2);
lean_dec(v_unused_884_);
v___x_858_ = v_dt_853_;
v_isShared_859_ = v_isSharedCheck_883_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_month_856_);
lean_inc(v_year_855_);
lean_dec(v_dt_853_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_883_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
uint8_t v___y_861_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; uint8_t v___y_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_870_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_871_ = lean_int_mod(v_year_855_, v___x_870_);
v___x_872_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_873_ = lean_int_dec_eq(v___x_871_, v___x_872_);
lean_dec(v___x_871_);
v___x_876_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_877_ = lean_int_mod(v_year_855_, v___x_876_);
v___x_878_ = lean_int_dec_eq(v___x_877_, v___x_872_);
lean_dec(v___x_877_);
if (v___x_878_ == 0)
{
uint8_t v___x_879_; 
v___x_879_ = 1;
v___y_875_ = v___x_879_;
goto v___jp_874_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_880_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_881_ = lean_int_mod(v_year_855_, v___x_880_);
v___x_882_ = lean_int_dec_eq(v___x_881_, v___x_872_);
lean_dec(v___x_881_);
v___y_875_ = v___x_882_;
goto v___jp_874_;
}
v___jp_860_:
{
lean_object* v_max_862_; uint8_t v___x_863_; 
v_max_862_ = l_Std_Time_Month_Ordinal_days(v___y_861_, v_month_856_);
v___x_863_ = lean_int_dec_lt(v_max_862_, v_days_854_);
if (v___x_863_ == 0)
{
lean_object* v___x_865_; 
lean_dec(v_max_862_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 2, v_days_854_);
v___x_865_ = v___x_858_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_year_855_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_month_856_);
lean_ctor_set(v_reuseFailAlloc_866_, 2, v_days_854_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
else
{
lean_object* v___x_868_; 
lean_dec(v_days_854_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 2, v_max_862_);
v___x_868_ = v___x_858_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_year_855_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_month_856_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_max_862_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
v___jp_874_:
{
if (v___x_873_ == 0)
{
v___y_861_ = v___x_873_;
goto v___jp_860_;
}
else
{
v___y_861_ = v___y_875_;
goto v___jp_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver(lean_object* v_dt_885_, lean_object* v_days_886_){
_start:
{
lean_object* v_year_887_; lean_object* v_month_888_; lean_object* v___x_889_; 
v_year_887_ = lean_ctor_get(v_dt_885_, 0);
lean_inc(v_year_887_);
v_month_888_ = lean_ctor_get(v_dt_885_, 1);
lean_inc(v_month_888_);
lean_dec_ref(v_dt_885_);
v___x_889_ = l_Std_Time_PlainDate_rollOver(v_year_887_, v_month_888_, v_days_886_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver___boxed(lean_object* v_dt_890_, lean_object* v_days_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Time_PlainDate_withDaysRollOver(v_dt_890_, v_days_891_);
lean_dec(v_days_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip(lean_object* v_dt_893_, lean_object* v_month_894_){
_start:
{
lean_object* v_year_895_; lean_object* v_day_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_923_; 
v_year_895_ = lean_ctor_get(v_dt_893_, 0);
v_day_896_ = lean_ctor_get(v_dt_893_, 2);
v_isSharedCheck_923_ = !lean_is_exclusive(v_dt_893_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_dt_893_, 1);
lean_dec(v_unused_924_);
v___x_898_ = v_dt_893_;
v_isShared_899_ = v_isSharedCheck_923_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_day_896_);
lean_inc(v_year_895_);
lean_dec(v_dt_893_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_923_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
uint8_t v___y_901_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; uint8_t v___y_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_910_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_911_ = lean_int_mod(v_year_895_, v___x_910_);
v___x_912_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_913_ = lean_int_dec_eq(v___x_911_, v___x_912_);
lean_dec(v___x_911_);
v___x_916_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_917_ = lean_int_mod(v_year_895_, v___x_916_);
v___x_918_ = lean_int_dec_eq(v___x_917_, v___x_912_);
lean_dec(v___x_917_);
if (v___x_918_ == 0)
{
uint8_t v___x_919_; 
v___x_919_ = 1;
v___y_915_ = v___x_919_;
goto v___jp_914_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_920_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_921_ = lean_int_mod(v_year_895_, v___x_920_);
v___x_922_ = lean_int_dec_eq(v___x_921_, v___x_912_);
lean_dec(v___x_921_);
v___y_915_ = v___x_922_;
goto v___jp_914_;
}
v___jp_900_:
{
lean_object* v_max_902_; uint8_t v___x_903_; 
v_max_902_ = l_Std_Time_Month_Ordinal_days(v___y_901_, v_month_894_);
v___x_903_ = lean_int_dec_lt(v_max_902_, v_day_896_);
if (v___x_903_ == 0)
{
lean_object* v___x_905_; 
lean_dec(v_max_902_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v_month_894_);
v___x_905_ = v___x_898_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_year_895_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_month_894_);
lean_ctor_set(v_reuseFailAlloc_906_, 2, v_day_896_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
else
{
lean_object* v___x_908_; 
lean_dec(v_day_896_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 2, v_max_902_);
lean_ctor_set(v___x_898_, 1, v_month_894_);
v___x_908_ = v___x_898_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_year_895_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_month_894_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_max_902_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
v___jp_914_:
{
if (v___x_913_ == 0)
{
v___y_901_ = v___x_913_;
goto v___jp_900_;
}
else
{
v___y_901_ = v___y_915_;
goto v___jp_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthRollOver(lean_object* v_dt_925_, lean_object* v_month_926_){
_start:
{
lean_object* v_year_927_; lean_object* v_day_928_; lean_object* v___x_929_; 
v_year_927_ = lean_ctor_get(v_dt_925_, 0);
lean_inc(v_year_927_);
v_day_928_ = lean_ctor_get(v_dt_925_, 2);
lean_inc(v_day_928_);
lean_dec_ref(v_dt_925_);
v___x_929_ = l_Std_Time_PlainDate_rollOver(v_year_927_, v_month_926_, v_day_928_);
lean_dec(v_day_928_);
return v___x_929_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__0(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_931_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_932_ = lean_int_sub(v___x_931_, v___x_930_);
return v___x_932_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_range_935_; 
v___x_933_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_934_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__0, &l_Std_Time_PlainDate_weekday___closed__0_once, _init_l_Std_Time_PlainDate_weekday___closed__0);
v_range_935_ = lean_int_add(v___x_934_, v___x_933_);
return v_range_935_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__2(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_937_ = lean_int_neg(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__3(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_unsigned_to_nat(6u);
v___x_939_ = lean_nat_to_int(v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_weekday(lean_object* v_date_940_){
_start:
{
lean_object* v___y_942_; lean_object* v_days_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v_days_951_ = l_Std_Time_PlainDate_toEpochDay(v_date_940_);
v___x_952_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_953_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__2, &l_Std_Time_PlainDate_weekday___closed__2_once, _init_l_Std_Time_PlainDate_weekday___closed__2);
v___x_954_ = lean_int_dec_le(v___x_953_, v_days_951_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_955_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_956_ = lean_int_add(v_days_951_, v___x_955_);
lean_dec(v_days_951_);
v___x_957_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_958_ = lean_int_emod(v___x_956_, v___x_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__3, &l_Std_Time_PlainDate_weekday___closed__3_once, _init_l_Std_Time_PlainDate_weekday___closed__3);
v___x_960_ = lean_int_add(v___x_958_, v___x_959_);
lean_dec(v___x_958_);
v___y_942_ = v___x_960_;
goto v___jp_941_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_961_ = lean_int_add(v_days_951_, v___x_952_);
lean_dec(v_days_951_);
v___x_962_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_963_ = lean_int_emod(v___x_961_, v___x_962_);
lean_dec(v___x_961_);
v___y_942_ = v___x_963_;
goto v___jp_941_;
}
v___jp_941_:
{
lean_object* v___x_943_; lean_object* v_range_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_943_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_range_944_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__1, &l_Std_Time_PlainDate_weekday___closed__1_once, _init_l_Std_Time_PlainDate_weekday___closed__1);
v___x_945_ = lean_int_sub(v___y_942_, v___x_943_);
lean_dec(v___y_942_);
v___x_946_ = lean_int_emod(v___x_945_, v_range_944_);
lean_dec(v___x_945_);
v___x_947_ = lean_int_add(v___x_946_, v_range_944_);
lean_dec(v___x_946_);
v___x_948_ = lean_int_emod(v___x_947_, v_range_944_);
lean_dec(v___x_947_);
v___x_949_ = lean_int_add(v___x_948_, v___x_943_);
lean_dec(v___x_948_);
v___x_950_ = l_Std_Time_Weekday_ofOrdinal(v___x_949_);
lean_dec(v___x_949_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekday___boxed(lean_object* v_date_964_){
_start:
{
uint8_t v_res_965_; lean_object* v_r_966_; 
v_res_965_ = l_Std_Time_PlainDate_weekday(v_date_964_);
v_r_966_ = lean_box(v_res_965_);
return v_r_966_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfMonth___closed__0(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_968_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__3, &l_Std_Time_PlainDate_weekday___closed__3_once, _init_l_Std_Time_PlainDate_weekday___closed__3);
v___x_969_ = lean_int_sub(v___x_968_, v___x_967_);
return v___x_969_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfMonth___closed__1(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_range_972_; 
v___x_970_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_971_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v_range_972_ = lean_int_add(v___x_971_, v___x_970_);
return v_range_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object* v_date_973_, uint8_t v_firstDay_974_){
_start:
{
lean_object* v_year_975_; lean_object* v_month_976_; lean_object* v_day_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1025_; 
v_year_975_ = lean_ctor_get(v_date_973_, 0);
v_month_976_ = lean_ctor_get(v_date_973_, 1);
v_day_977_ = lean_ctor_get(v_date_973_, 2);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_date_973_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_979_ = v_date_973_;
v_isShared_980_ = v_isSharedCheck_1025_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_day_977_);
lean_inc(v_month_976_);
lean_inc(v_year_975_);
lean_dec(v_date_973_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1025_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___y_982_; lean_object* v___x_1001_; uint8_t v___y_1003_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; uint8_t v___y_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1001_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_1012_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_1013_ = lean_int_mod(v_year_975_, v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1015_ = lean_int_dec_eq(v___x_1013_, v___x_1014_);
lean_dec(v___x_1013_);
v___x_1018_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_1019_ = lean_int_mod(v_year_975_, v___x_1018_);
v___x_1020_ = lean_int_dec_eq(v___x_1019_, v___x_1014_);
lean_dec(v___x_1019_);
if (v___x_1020_ == 0)
{
uint8_t v___x_1021_; 
v___x_1021_ = 1;
v___y_1017_ = v___x_1021_;
goto v___jp_1016_;
}
else
{
lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1022_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_1023_ = lean_int_mod(v_year_975_, v___x_1022_);
v___x_1024_ = lean_int_dec_eq(v___x_1023_, v___x_1014_);
lean_dec(v___x_1023_);
v___y_1017_ = v___x_1024_;
goto v___jp_1016_;
}
v___jp_981_:
{
uint8_t v___x_983_; lean_object* v_day1Ord_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_offset_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_range_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_983_ = l_Std_Time_PlainDate_weekday(v___y_982_);
v_day1Ord_984_ = l_Std_Time_Weekday_toOrdinal(v___x_983_);
v___x_985_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_974_);
v___x_986_ = lean_int_sub(v_day1Ord_984_, v___x_985_);
lean_dec(v___x_985_);
lean_dec(v_day1Ord_984_);
v___x_987_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_988_ = lean_int_add(v___x_986_, v___x_987_);
lean_dec(v___x_986_);
v_offset_989_ = lean_int_emod(v___x_988_, v___x_987_);
lean_dec(v___x_988_);
v___x_990_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_991_ = lean_int_sub(v_day_977_, v___x_990_);
lean_dec(v_day_977_);
v___x_992_ = lean_int_add(v___x_991_, v_offset_989_);
lean_dec(v_offset_989_);
lean_dec(v___x_991_);
v___x_993_ = lean_int_ediv(v___x_992_, v___x_987_);
lean_dec(v___x_992_);
v___x_994_ = lean_int_add(v___x_993_, v___x_990_);
lean_dec(v___x_993_);
v_range_995_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__1, &l_Std_Time_PlainDate_weekOfMonth___closed__1_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__1);
v___x_996_ = lean_int_sub(v___x_994_, v___x_990_);
lean_dec(v___x_994_);
v___x_997_ = lean_int_emod(v___x_996_, v_range_995_);
lean_dec(v___x_996_);
v___x_998_ = lean_int_add(v___x_997_, v_range_995_);
lean_dec(v___x_997_);
v___x_999_ = lean_int_emod(v___x_998_, v_range_995_);
lean_dec(v___x_998_);
v___x_1000_ = lean_int_add(v___x_999_, v___x_990_);
lean_dec(v___x_999_);
return v___x_1000_;
}
v___jp_1002_:
{
lean_object* v_max_1004_; uint8_t v___x_1005_; 
v_max_1004_ = l_Std_Time_Month_Ordinal_days(v___y_1003_, v_month_976_);
v___x_1005_ = lean_int_dec_lt(v_max_1004_, v___x_1001_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1007_; 
lean_dec(v_max_1004_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 2, v___x_1001_);
v___x_1007_ = v___x_979_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_year_975_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_month_976_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v___x_1001_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
v___y_982_ = v___x_1007_;
goto v___jp_981_;
}
}
else
{
lean_object* v___x_1010_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 2, v_max_1004_);
v___x_1010_ = v___x_979_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_year_975_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_month_976_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_max_1004_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
v___y_982_ = v___x_1010_;
goto v___jp_981_;
}
}
}
v___jp_1016_:
{
if (v___x_1015_ == 0)
{
v___y_1003_ = v___x_1015_;
goto v___jp_1002_;
}
else
{
v___y_1003_ = v___y_1017_;
goto v___jp_1002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object* v_date_1026_, lean_object* v_firstDay_1027_){
_start:
{
uint8_t v_firstDay_boxed_1028_; lean_object* v_res_1029_; 
v_firstDay_boxed_1028_ = lean_unbox(v_firstDay_1027_);
v_res_1029_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1026_, v_firstDay_boxed_1028_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday(lean_object* v_date_1030_, uint8_t v_desiredWeekday_1031_){
_start:
{
lean_object* v___y_1033_; uint8_t v___x_1037_; lean_object* v_weekday_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
lean_inc_ref(v_date_1030_);
v___x_1037_ = l_Std_Time_PlainDate_weekday(v_date_1030_);
v_weekday_1038_ = l_Std_Time_Weekday_toOrdinal(v___x_1037_);
v___x_1039_ = l_Std_Time_Weekday_toOrdinal(v_desiredWeekday_1031_);
v___x_1040_ = lean_int_neg(v_weekday_1038_);
lean_dec(v_weekday_1038_);
v___x_1041_ = lean_int_add(v___x_1039_, v___x_1040_);
lean_dec(v___x_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1043_ = lean_int_dec_lt(v___x_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
v___y_1033_ = v___x_1041_;
goto v___jp_1032_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1045_ = lean_int_add(v___x_1041_, v___x_1044_);
lean_dec(v___x_1041_);
v___y_1033_ = v___x_1045_;
goto v___jp_1032_;
}
v___jp_1032_:
{
lean_object* v_dateDays_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_dateDays_1034_ = l_Std_Time_PlainDate_toEpochDay(v_date_1030_);
v___x_1035_ = lean_int_add(v_dateDays_1034_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec(v_dateDays_1034_);
v___x_1036_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1035_);
lean_dec(v___x_1035_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object* v_date_1046_, lean_object* v_desiredWeekday_1047_){
_start:
{
uint8_t v_desiredWeekday_boxed_1048_; lean_object* v_res_1049_; 
v_desiredWeekday_boxed_1048_ = lean_unbox(v_desiredWeekday_1047_);
v_res_1049_ = l_Std_Time_PlainDate_withWeekday(v_date_1046_, v_desiredWeekday_boxed_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(uint8_t v_weekday_1050_, uint8_t v_firstDay_1051_){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1052_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1053_ = l_Std_Time_Weekday_toOrdinal(v_weekday_1050_);
v___x_1054_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_1051_);
v___x_1055_ = lean_int_neg(v___x_1054_);
lean_dec(v___x_1054_);
v___x_1056_ = lean_int_add(v___x_1053_, v___x_1055_);
lean_dec(v___x_1055_);
lean_dec(v___x_1053_);
v___x_1057_ = lean_int_emod(v___x_1056_, v___x_1052_);
lean_dec(v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek___boxed(lean_object* v_weekday_1058_, lean_object* v_firstDay_1059_){
_start:
{
uint8_t v_weekday_boxed_1060_; uint8_t v_firstDay_boxed_1061_; lean_object* v_res_1062_; 
v_weekday_boxed_1060_ = lean_unbox(v_weekday_1058_);
v_firstDay_boxed_1061_ = lean_unbox(v_firstDay_1059_);
v_res_1062_ = l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(v_weekday_boxed_1060_, v_firstDay_boxed_1061_);
return v_res_1062_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(11u);
v___x_1064_ = lean_nat_to_int(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0);
v___x_1066_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1067_ = lean_int_add(v___x_1066_, v___x_1065_);
return v___x_1067_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1069_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1);
v___x_1070_ = lean_int_sub(v___x_1069_, v___x_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v_range_1073_; 
v___x_1071_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1072_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2);
v_range_1073_ = lean_int_add(v___x_1072_, v___x_1071_);
return v_range_1073_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4(void){
_start:
{
lean_object* v_range_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_range_1074_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1075_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_1076_ = lean_int_emod(v___x_1075_, v_range_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5(void){
_start:
{
lean_object* v_range_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_range_1077_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1078_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4);
v___x_1079_ = lean_int_add(v___x_1078_, v_range_1077_);
return v___x_1079_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6(void){
_start:
{
lean_object* v_range_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_range_1080_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1081_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5);
v___x_1082_ = lean_int_emod(v___x_1081_, v_range_1080_);
return v___x_1082_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1084_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6);
v___x_1085_ = lean_int_add(v___x_1084_, v___x_1083_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear(lean_object* v_year_1086_, uint8_t v_firstDay_1087_, lean_object* v_minimalDays_1088_){
_start:
{
lean_object* v___y_1090_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___y_1109_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; uint8_t v___y_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1106_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7);
v___x_1107_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_1114_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_1115_ = lean_int_mod(v_year_1086_, v___x_1114_);
v___x_1116_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1117_ = lean_int_dec_eq(v___x_1115_, v___x_1116_);
lean_dec(v___x_1115_);
v___x_1120_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_1121_ = lean_int_mod(v_year_1086_, v___x_1120_);
v___x_1122_ = lean_int_dec_eq(v___x_1121_, v___x_1116_);
lean_dec(v___x_1121_);
if (v___x_1122_ == 0)
{
uint8_t v___x_1123_; 
v___x_1123_ = 1;
v___y_1119_ = v___x_1123_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1124_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_1125_ = lean_int_mod(v_year_1086_, v___x_1124_);
v___x_1126_ = lean_int_dec_eq(v___x_1125_, v___x_1116_);
lean_dec(v___x_1125_);
v___y_1119_ = v___x_1126_;
goto v___jp_1118_;
}
v___jp_1089_:
{
uint8_t v___x_1091_; lean_object* v_localDay_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_dateDays_1099_; lean_object* v___x_1100_; lean_object* v_weekStart_1101_; uint8_t v___x_1102_; 
lean_inc_ref(v___y_1090_);
v___x_1091_ = l_Std_Time_PlainDate_weekday(v___y_1090_);
v_localDay_1092_ = l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(v___x_1091_, v_firstDay_1087_);
v___x_1093_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1094_ = lean_int_neg(v_localDay_1092_);
v___x_1095_ = lean_int_add(v___x_1093_, v___x_1094_);
lean_dec(v___x_1094_);
v___x_1096_ = l_Int_toNat(v_localDay_1092_);
lean_dec(v_localDay_1092_);
v___x_1097_ = lean_nat_to_int(v___x_1096_);
v___x_1098_ = lean_int_neg(v___x_1097_);
lean_dec(v___x_1097_);
v_dateDays_1099_ = l_Std_Time_PlainDate_toEpochDay(v___y_1090_);
v___x_1100_ = lean_int_add(v_dateDays_1099_, v___x_1098_);
lean_dec(v___x_1098_);
lean_dec(v_dateDays_1099_);
v_weekStart_1101_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1100_);
lean_dec(v___x_1100_);
v___x_1102_ = lean_int_dec_le(v_minimalDays_1088_, v___x_1095_);
lean_dec(v___x_1095_);
if (v___x_1102_ == 0)
{
lean_object* v_dateDays_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_dateDays_1103_ = l_Std_Time_PlainDate_toEpochDay(v_weekStart_1101_);
v___x_1104_ = lean_int_add(v_dateDays_1103_, v___x_1093_);
lean_dec(v_dateDays_1103_);
v___x_1105_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1104_);
lean_dec(v___x_1104_);
return v___x_1105_;
}
else
{
return v_weekStart_1101_;
}
}
v___jp_1108_:
{
lean_object* v_max_1110_; uint8_t v___x_1111_; 
v_max_1110_ = l_Std_Time_Month_Ordinal_days(v___y_1109_, v___x_1106_);
v___x_1111_ = lean_int_dec_lt(v_max_1110_, v___x_1107_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_max_1110_);
v___x_1112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1112_, 0, v_year_1086_);
lean_ctor_set(v___x_1112_, 1, v___x_1106_);
lean_ctor_set(v___x_1112_, 2, v___x_1107_);
v___y_1090_ = v___x_1112_;
goto v___jp_1089_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1113_, 0, v_year_1086_);
lean_ctor_set(v___x_1113_, 1, v___x_1106_);
lean_ctor_set(v___x_1113_, 2, v_max_1110_);
v___y_1090_ = v___x_1113_;
goto v___jp_1089_;
}
}
v___jp_1118_:
{
if (v___x_1117_ == 0)
{
v___y_1109_ = v___x_1117_;
goto v___jp_1108_;
}
else
{
v___y_1109_ = v___y_1119_;
goto v___jp_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___boxed(lean_object* v_year_1127_, lean_object* v_firstDay_1128_, lean_object* v_minimalDays_1129_){
_start:
{
uint8_t v_firstDay_boxed_1130_; lean_object* v_res_1131_; 
v_firstDay_boxed_1130_ = lean_unbox(v_firstDay_1128_);
v_res_1131_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1127_, v_firstDay_boxed_1130_, v_minimalDays_1129_);
lean_dec(v_minimalDays_1129_);
return v_res_1131_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__0(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(370u);
v___x_1133_ = lean_nat_to_int(v___x_1132_);
return v___x_1133_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__1(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1135_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__0, &l_Std_Time_PlainDate_weekOfYear___closed__0_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__0);
v___x_1136_ = lean_int_sub(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__2(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v_range_1139_; 
v___x_1137_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1138_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__1, &l_Std_Time_PlainDate_weekOfYear___closed__1_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__1);
v_range_1139_ = lean_int_add(v___x_1138_, v___x_1137_);
return v_range_1139_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__3(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_unsigned_to_nat(52u);
v___x_1141_ = lean_nat_to_int(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__4(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__3, &l_Std_Time_PlainDate_weekOfYear___closed__3_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__3);
v___x_1143_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1144_ = lean_int_add(v___x_1143_, v___x_1142_);
return v___x_1144_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__5(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1146_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__4, &l_Std_Time_PlainDate_weekOfYear___closed__4_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__4);
v___x_1147_ = lean_int_sub(v___x_1146_, v___x_1145_);
return v___x_1147_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__6(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_range_1150_; 
v___x_1148_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1149_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__5, &l_Std_Time_PlainDate_weekOfYear___closed__5_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__5);
v_range_1150_ = lean_int_add(v___x_1149_, v___x_1148_);
return v_range_1150_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__7(void){
_start:
{
lean_object* v_range_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_range_1151_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1152_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_1153_ = lean_int_emod(v___x_1152_, v_range_1151_);
return v___x_1153_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__8(void){
_start:
{
lean_object* v_range_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_range_1154_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1155_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__7, &l_Std_Time_PlainDate_weekOfYear___closed__7_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__7);
v___x_1156_ = lean_int_add(v___x_1155_, v_range_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__9(void){
_start:
{
lean_object* v_range_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_range_1157_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1158_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__8, &l_Std_Time_PlainDate_weekOfYear___closed__8_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__8);
v___x_1159_ = lean_int_emod(v___x_1158_, v_range_1157_);
return v___x_1159_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__10(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1161_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__9, &l_Std_Time_PlainDate_weekOfYear___closed__9_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__9);
v___x_1162_ = lean_int_add(v___x_1161_, v___x_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object* v_date_1163_, uint8_t v_firstDay_1164_, lean_object* v_minDaysBounded_1165_){
_start:
{
lean_object* v_year_1166_; lean_object* v_thisYearStart_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_year_1166_ = lean_ctor_get(v_date_1163_, 0);
lean_inc_n(v_year_1166_, 2);
v_thisYearStart_1167_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1166_, v_firstDay_1164_, v_minDaysBounded_1165_);
v___x_1168_ = l_Std_Time_PlainDate_toEpochDay(v_date_1163_);
v___x_1169_ = l_Std_Time_PlainDate_toEpochDay(v_thisYearStart_1167_);
v___x_1170_ = lean_int_dec_lt(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_nextYearStart_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1171_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1172_ = lean_int_add(v_year_1166_, v___x_1171_);
lean_dec(v_year_1166_);
v_nextYearStart_1173_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1172_, v_firstDay_1164_, v_minDaysBounded_1165_);
v___x_1174_ = l_Std_Time_PlainDate_toEpochDay(v_nextYearStart_1173_);
v___x_1175_ = lean_int_dec_le(v___x_1174_, v___x_1168_);
lean_dec(v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_range_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1176_ = lean_int_sub(v___x_1168_, v___x_1169_);
lean_dec(v___x_1169_);
lean_dec(v___x_1168_);
v___x_1177_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v_range_1178_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__2, &l_Std_Time_PlainDate_weekOfYear___closed__2_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__2);
v___x_1179_ = lean_int_sub(v___x_1176_, v___x_1177_);
lean_dec(v___x_1176_);
v___x_1180_ = lean_int_emod(v___x_1179_, v_range_1178_);
lean_dec(v___x_1179_);
v___x_1181_ = lean_int_add(v___x_1180_, v_range_1178_);
lean_dec(v___x_1180_);
v___x_1182_ = lean_int_emod(v___x_1181_, v_range_1178_);
lean_dec(v___x_1181_);
v___x_1183_ = lean_int_add(v___x_1182_, v___x_1177_);
lean_dec(v___x_1182_);
v___x_1184_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1185_ = lean_int_ediv(v___x_1183_, v___x_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_int_add(v___x_1185_, v___x_1171_);
lean_dec(v___x_1185_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; 
lean_dec(v___x_1169_);
lean_dec(v___x_1168_);
v___x_1187_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__10, &l_Std_Time_PlainDate_weekOfYear___closed__10_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__10);
return v___x_1187_;
}
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_prevYearStart_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v_range_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec(v___x_1169_);
v___x_1188_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1189_ = lean_int_sub(v_year_1166_, v___x_1188_);
lean_dec(v_year_1166_);
v_prevYearStart_1190_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1189_, v_firstDay_1164_, v_minDaysBounded_1165_);
v___x_1191_ = l_Std_Time_PlainDate_toEpochDay(v_prevYearStart_1190_);
v___x_1192_ = lean_int_sub(v___x_1168_, v___x_1191_);
lean_dec(v___x_1191_);
lean_dec(v___x_1168_);
v___x_1193_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v_range_1194_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__2, &l_Std_Time_PlainDate_weekOfYear___closed__2_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__2);
v___x_1195_ = lean_int_sub(v___x_1192_, v___x_1193_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_int_emod(v___x_1195_, v_range_1194_);
lean_dec(v___x_1195_);
v___x_1197_ = lean_int_add(v___x_1196_, v_range_1194_);
lean_dec(v___x_1196_);
v___x_1198_ = lean_int_emod(v___x_1197_, v_range_1194_);
lean_dec(v___x_1197_);
v___x_1199_ = lean_int_add(v___x_1198_, v___x_1193_);
lean_dec(v___x_1198_);
v___x_1200_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1201_ = lean_int_ediv(v___x_1199_, v___x_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_int_add(v___x_1201_, v___x_1188_);
lean_dec(v___x_1201_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear___boxed(lean_object* v_date_1203_, lean_object* v_firstDay_1204_, lean_object* v_minDaysBounded_1205_){
_start:
{
uint8_t v_firstDay_boxed_1206_; lean_object* v_res_1207_; 
v_firstDay_boxed_1206_ = lean_unbox(v_firstDay_1204_);
v_res_1207_ = l_Std_Time_PlainDate_weekOfYear(v_date_1203_, v_firstDay_boxed_1206_, v_minDaysBounded_1205_);
lean_dec(v_minDaysBounded_1205_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekYear(lean_object* v_date_1208_, uint8_t v_firstDay_1209_, lean_object* v_minDays_1210_){
_start:
{
lean_object* v_year_1211_; lean_object* v_thisYearStart_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v_year_1211_ = lean_ctor_get(v_date_1208_, 0);
lean_inc_n(v_year_1211_, 2);
v_thisYearStart_1212_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1211_, v_firstDay_1209_, v_minDays_1210_);
v___x_1213_ = l_Std_Time_PlainDate_toEpochDay(v_date_1208_);
v___x_1214_ = l_Std_Time_PlainDate_toEpochDay(v_thisYearStart_1212_);
v___x_1215_ = lean_int_dec_lt(v___x_1213_, v___x_1214_);
lean_dec(v___x_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_nextYearStart_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1216_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1217_ = lean_int_add(v_year_1211_, v___x_1216_);
lean_inc(v___x_1217_);
v_nextYearStart_1218_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1217_, v_firstDay_1209_, v_minDays_1210_);
v___x_1219_ = l_Std_Time_PlainDate_toEpochDay(v_nextYearStart_1218_);
v___x_1220_ = lean_int_dec_le(v___x_1219_, v___x_1213_);
lean_dec(v___x_1213_);
lean_dec(v___x_1219_);
if (v___x_1220_ == 0)
{
lean_dec(v___x_1217_);
return v_year_1211_;
}
else
{
lean_dec(v_year_1211_);
return v___x_1217_;
}
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec(v___x_1213_);
v___x_1221_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1222_ = lean_int_sub(v_year_1211_, v___x_1221_);
lean_dec(v_year_1211_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekYear___boxed(lean_object* v_date_1223_, lean_object* v_firstDay_1224_, lean_object* v_minDays_1225_){
_start:
{
uint8_t v_firstDay_boxed_1226_; lean_object* v_res_1227_; 
v_firstDay_boxed_1226_ = lean_unbox(v_firstDay_1224_);
v_res_1227_ = l_Std_Time_PlainDate_weekYear(v_date_1223_, v_firstDay_boxed_1226_, v_minDays_1225_);
lean_dec(v_minDays_1225_);
return v_res_1227_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Year(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_PlainDate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
