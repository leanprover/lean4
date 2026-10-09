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
lean_object* v_year_47_; lean_object* v_month_48_; lean_object* v_day_49_; lean_object* v___x_50_; lean_object* v___y_52_; lean_object* v___y_53_; uint8_t v___y_54_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___y_89_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
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
lean_inc(v___y_56_);
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___y_56_);
lean_ctor_set(v___x_58_, 1, v___y_57_);
v___x_59_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v___y_54_);
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
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___y_54_);
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
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___y_54_);
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
v___y_54_ = v___x_91_;
v___y_55_ = v___x_94_;
v___y_56_ = v___x_101_;
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
v___y_54_ = v___x_91_;
v___y_55_ = v___x_94_;
v___y_56_ = v___x_101_;
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
uint8_t l_Std_Time_instDecidableEqPlainDate_decEq(lean_object* v_x_128_, lean_object* v_x_129_){
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
LEAN_EXPORT void l_Std_Time_instDecidableEqPlainDate_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_128_ = stack[0].m_obj;
lean_object* v_x_129_ = stack[1].m_obj;
uint8_t v_res_139_;
v_res_139_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_128_, v_x_129_);
stack->m_num = v_res_139_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDate_decEq___boxed(lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_140_, v_x_141_);
lean_dec_ref(v_x_141_);
lean_dec_ref(v_x_140_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
uint8_t l_Std_Time_instDecidableEqPlainDate(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_144_, v_x_145_);
return v___x_146_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqPlainDate_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_144_ = stack[0].m_obj;
lean_object* v_x_145_ = stack[1].m_obj;
uint8_t v_res_147_;
v_res_147_ = l_Std_Time_instDecidableEqPlainDate(v_x_144_, v_x_145_);
stack->m_num = v_res_147_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainDate___boxed(lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Std_Time_instDecidableEqPlainDate(v_x_148_, v_x_149_);
lean_dec_ref(v_x_149_);
lean_dec_ref(v_x_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__0(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__1(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(11u);
v___x_155_ = lean_nat_to_int(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__1, &l_Std_Time_instInhabitedPlainDate___closed__1_once, _init_l_Std_Time_instInhabitedPlainDate___closed__1);
v___x_157_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_158_ = lean_int_add(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_160_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__2, &l_Std_Time_instInhabitedPlainDate___closed__2_once, _init_l_Std_Time_instInhabitedPlainDate___closed__2);
v___x_161_ = lean_int_sub(v___x_160_, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__4(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_range_164_; 
v___x_162_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_163_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__3, &l_Std_Time_instInhabitedPlainDate___closed__3_once, _init_l_Std_Time_instInhabitedPlainDate___closed__3);
v_range_164_ = lean_int_add(v___x_163_, v___x_162_);
return v_range_164_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__5(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_166_ = lean_int_sub(v___x_165_, v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__6(void){
_start:
{
lean_object* v_range_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_range_167_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__4, &l_Std_Time_instInhabitedPlainDate___closed__4_once, _init_l_Std_Time_instInhabitedPlainDate___closed__4);
v___x_168_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_169_ = lean_int_emod(v___x_168_, v_range_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__7(void){
_start:
{
lean_object* v_range_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_range_170_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__4, &l_Std_Time_instInhabitedPlainDate___closed__4_once, _init_l_Std_Time_instInhabitedPlainDate___closed__4);
v___x_171_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__6, &l_Std_Time_instInhabitedPlainDate___closed__6_once, _init_l_Std_Time_instInhabitedPlainDate___closed__6);
v___x_172_ = lean_int_add(v___x_171_, v_range_170_);
return v___x_172_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__8(void){
_start:
{
lean_object* v_range_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_range_173_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__4, &l_Std_Time_instInhabitedPlainDate___closed__4_once, _init_l_Std_Time_instInhabitedPlainDate___closed__4);
v___x_174_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__7, &l_Std_Time_instInhabitedPlainDate___closed__7_once, _init_l_Std_Time_instInhabitedPlainDate___closed__7);
v___x_175_ = lean_int_emod(v___x_174_, v_range_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__9(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_177_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__8, &l_Std_Time_instInhabitedPlainDate___closed__8_once, _init_l_Std_Time_instInhabitedPlainDate___closed__8);
v___x_178_ = lean_int_add(v___x_177_, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__10(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(30u);
v___x_180_ = lean_nat_to_int(v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__11(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__10, &l_Std_Time_instInhabitedPlainDate___closed__10_once, _init_l_Std_Time_instInhabitedPlainDate___closed__10);
v___x_182_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_183_ = lean_int_add(v___x_182_, v___x_181_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__12(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_185_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__11, &l_Std_Time_instInhabitedPlainDate___closed__11_once, _init_l_Std_Time_instInhabitedPlainDate___closed__11);
v___x_186_ = lean_int_sub(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__13(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_range_189_; 
v___x_187_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_188_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__12, &l_Std_Time_instInhabitedPlainDate___closed__12_once, _init_l_Std_Time_instInhabitedPlainDate___closed__12);
v_range_189_ = lean_int_add(v___x_188_, v___x_187_);
return v_range_189_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__14(void){
_start:
{
lean_object* v_range_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_range_190_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__13, &l_Std_Time_instInhabitedPlainDate___closed__13_once, _init_l_Std_Time_instInhabitedPlainDate___closed__13);
v___x_191_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_192_ = lean_int_emod(v___x_191_, v_range_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__15(void){
_start:
{
lean_object* v_range_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_range_193_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__13, &l_Std_Time_instInhabitedPlainDate___closed__13_once, _init_l_Std_Time_instInhabitedPlainDate___closed__13);
v___x_194_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__14, &l_Std_Time_instInhabitedPlainDate___closed__14_once, _init_l_Std_Time_instInhabitedPlainDate___closed__14);
v___x_195_ = lean_int_add(v___x_194_, v_range_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__16(void){
_start:
{
lean_object* v_range_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_range_196_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__13, &l_Std_Time_instInhabitedPlainDate___closed__13_once, _init_l_Std_Time_instInhabitedPlainDate___closed__13);
v___x_197_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__15, &l_Std_Time_instInhabitedPlainDate___closed__15_once, _init_l_Std_Time_instInhabitedPlainDate___closed__15);
v___x_198_ = lean_int_emod(v___x_197_, v_range_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__17(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_200_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__16, &l_Std_Time_instInhabitedPlainDate___closed__16_once, _init_l_Std_Time_instInhabitedPlainDate___closed__16);
v___x_201_ = lean_int_add(v___x_200_, v___x_199_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate___closed__18(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_202_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__17, &l_Std_Time_instInhabitedPlainDate___closed__17_once, _init_l_Std_Time_instInhabitedPlainDate___closed__17);
v___x_203_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__9, &l_Std_Time_instInhabitedPlainDate___closed__9_once, _init_l_Std_Time_instInhabitedPlainDate___closed__9);
v___x_204_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_202_);
return v___x_205_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainDate(void){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__18, &l_Std_Time_instInhabitedPlainDate___closed__18_once, _init_l_Std_Time_instInhabitedPlainDate___closed__18);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0(lean_object* v_x_207_){
_start:
{
lean_object* v_year_208_; 
v_year_208_ = lean_ctor_get(v_x_207_, 0);
lean_inc(v_year_208_);
return v_year_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__0___boxed(lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Time_instOrdPlainDate___lam__0(v_x_209_);
lean_dec_ref(v_x_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1(lean_object* v_x_211_){
_start:
{
lean_object* v_month_212_; 
v_month_212_ = lean_ctor_get(v_x_211_, 1);
lean_inc(v_month_212_);
return v_month_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__1___boxed(lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Time_instOrdPlainDate___lam__1(v_x_213_);
lean_dec_ref(v_x_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2(lean_object* v_x_215_){
_start:
{
lean_object* v_day_216_; 
v_day_216_ = lean_ctor_get(v_x_215_, 2);
lean_inc(v_day_216_);
return v_day_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate___lam__2___boxed(lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Time_instOrdPlainDate___lam__2(v_x_217_);
lean_dec_ref(v_x_217_);
return v_res_218_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(4u);
v___x_242_ = lean_nat_to_int(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(400u);
v___x_244_ = lean_nat_to_int(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(100u);
v___x_246_ = lean_nat_to_int(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip(lean_object* v_year_247_, lean_object* v_month_248_, lean_object* v_day_249_){
_start:
{
uint8_t v___y_251_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_263_; 
v___x_256_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_257_ = lean_int_mod(v_year_247_, v___x_256_);
v___x_258_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_263_ = lean_int_dec_eq(v___x_257_, v___x_258_);
lean_dec(v___x_257_);
if (v___x_263_ == 0)
{
v___y_251_ = v___x_263_;
goto v___jp_250_;
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_265_ = lean_int_mod(v_year_247_, v___x_264_);
v___x_266_ = lean_int_dec_eq(v___x_265_, v___x_258_);
lean_dec(v___x_265_);
if (v___x_266_ == 0)
{
if (v___x_263_ == 0)
{
goto v___jp_259_;
}
else
{
v___y_251_ = v___x_263_;
goto v___jp_250_;
}
}
else
{
goto v___jp_259_;
}
}
v___jp_250_:
{
lean_object* v_max_252_; uint8_t v___x_253_; 
v_max_252_ = l_Std_Time_Month_Ordinal_days(v___y_251_, v_month_248_);
v___x_253_ = lean_int_dec_lt(v_max_252_, v_day_249_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_max_252_);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v_year_247_);
lean_ctor_set(v___x_254_, 1, v_month_248_);
lean_ctor_set(v___x_254_, 2, v_day_249_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; 
lean_dec(v_day_249_);
v___x_255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_255_, 0, v_year_247_);
lean_ctor_set(v___x_255_, 1, v_month_248_);
lean_ctor_set(v___x_255_, 2, v_max_252_);
return v___x_255_;
}
}
v___jp_259_:
{
lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_260_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_261_ = lean_int_mod(v_year_247_, v___x_260_);
v___x_262_ = lean_int_dec_eq(v___x_261_, v___x_258_);
lean_dec(v___x_261_);
v___y_251_ = v___x_262_;
goto v___jp_250_;
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
uint8_t v___y_276_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_289_; 
v___x_282_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_283_ = lean_int_mod(v_year_272_, v___x_282_);
v___x_284_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_289_ = lean_int_dec_eq(v___x_283_, v___x_284_);
lean_dec(v___x_283_);
if (v___x_289_ == 0)
{
v___y_276_ = v___x_289_;
goto v___jp_275_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_291_ = lean_int_mod(v_year_272_, v___x_290_);
v___x_292_ = lean_int_dec_eq(v___x_291_, v___x_284_);
lean_dec(v___x_291_);
if (v___x_292_ == 0)
{
if (v___x_289_ == 0)
{
goto v___jp_285_;
}
else
{
v___y_276_ = v___x_289_;
goto v___jp_275_;
}
}
else
{
goto v___jp_285_;
}
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
v___jp_285_:
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_287_ = lean_int_mod(v_year_272_, v___x_286_);
v___x_288_ = lean_int_dec_eq(v___x_287_, v___x_284_);
lean_dec(v___x_287_);
v___y_276_ = v___x_288_;
goto v___jp_275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal(lean_object* v_year_293_, lean_object* v_ordinal_294_){
_start:
{
uint8_t v___y_296_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_308_; 
v___x_301_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_302_ = lean_int_mod(v_year_293_, v___x_301_);
v___x_303_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_308_ = lean_int_dec_eq(v___x_302_, v___x_303_);
lean_dec(v___x_302_);
if (v___x_308_ == 0)
{
v___y_296_ = v___x_308_;
goto v___jp_295_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_309_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_310_ = lean_int_mod(v_year_293_, v___x_309_);
v___x_311_ = lean_int_dec_eq(v___x_310_, v___x_303_);
lean_dec(v___x_310_);
if (v___x_311_ == 0)
{
if (v___x_308_ == 0)
{
goto v___jp_304_;
}
else
{
v___y_296_ = v___x_308_;
goto v___jp_295_;
}
}
else
{
goto v___jp_304_;
}
}
v___jp_295_:
{
lean_object* v_val_297_; lean_object* v_fst_298_; lean_object* v_snd_299_; lean_object* v___x_300_; 
v_val_297_ = l_Std_Time_ValidDate_ofOrdinal(v___y_296_, v_ordinal_294_);
v_fst_298_ = lean_ctor_get(v_val_297_, 0);
lean_inc(v_fst_298_);
v_snd_299_ = lean_ctor_get(v_val_297_, 1);
lean_inc(v_snd_299_);
lean_dec_ref(v_val_297_);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v_year_293_);
lean_ctor_set(v___x_300_, 1, v_fst_298_);
lean_ctor_set(v___x_300_, 2, v_snd_299_);
return v___x_300_;
}
v___jp_304_:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_306_ = lean_int_mod(v_year_293_, v___x_305_);
v___x_307_ = lean_int_dec_eq(v___x_306_, v___x_303_);
lean_dec(v___x_306_);
v___y_296_ = v___x_307_;
goto v___jp_295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal___boxed(lean_object* v_year_312_, lean_object* v_ordinal_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Time_PlainDate_ofYearOrdinal(v_year_312_, v_ordinal_313_);
lean_dec(v_ordinal_313_);
return v_res_314_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__0(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(719468u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__1(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(31u);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__2(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(12u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__3(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(146097u);
v___x_322_ = lean_nat_to_int(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__4(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(1460u);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__5(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(36524u);
v___x_326_ = lean_nat_to_int(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__6(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(146096u);
v___x_328_ = lean_nat_to_int(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__7(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(365u);
v___x_330_ = lean_nat_to_int(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__8(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(5u);
v___x_332_ = lean_nat_to_int(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__9(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = lean_nat_to_int(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__10(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(153u);
v___x_336_ = lean_nat_to_int(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__11(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(10u);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__12(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___x_340_ = lean_int_neg(v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__13(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(3u);
v___x_342_ = lean_nat_to_int(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object* v_day_343_){
_start:
{
lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; uint8_t v___y_348_; lean_object* v___x_353_; lean_object* v_z_354_; lean_object* v___x_355_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_404_; lean_object* v___y_405_; lean_object* v___y_406_; lean_object* v___y_407_; lean_object* v___y_411_; uint8_t v___x_454_; 
v___x_353_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__0, &l_Std_Time_PlainDate_ofEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__0);
v_z_354_ = lean_int_add(v_day_343_, v___x_353_);
v___x_355_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_454_ = lean_int_dec_le(v___x_355_, v_z_354_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__6, &l_Std_Time_PlainDate_ofEpochDay___closed__6_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__6);
v___x_456_ = lean_int_sub(v_z_354_, v___x_455_);
v___y_411_ = v___x_456_;
goto v___jp_410_;
}
else
{
lean_inc(v_z_354_);
v___y_411_ = v_z_354_;
goto v___jp_410_;
}
v___jp_344_:
{
lean_object* v_max_349_; uint8_t v___x_350_; 
v_max_349_ = l_Std_Time_Month_Ordinal_days(v___y_348_, v___y_346_);
v___x_350_ = lean_int_dec_lt(v_max_349_, v___y_345_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; 
lean_dec(v_max_349_);
v___x_351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_351_, 0, v___y_347_);
lean_ctor_set(v___x_351_, 1, v___y_346_);
lean_ctor_set(v___x_351_, 2, v___y_345_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; 
lean_dec(v___y_345_);
v___x_352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_352_, 0, v___y_347_);
lean_ctor_set(v___x_352_, 1, v___y_346_);
lean_ctor_set(v___x_352_, 2, v_max_349_);
return v___x_352_;
}
}
v___jp_356_:
{
lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_361_ = lean_int_mod(v___y_359_, v___y_360_);
v___x_362_ = lean_int_dec_eq(v___x_361_, v___x_355_);
lean_dec(v___x_361_);
v___y_345_ = v___y_357_;
v___y_346_ = v___y_358_;
v___y_347_ = v___y_359_;
v___y_348_ = v___x_362_;
goto v___jp_344_;
}
v___jp_363_:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_int_mod(v___y_367_, v___y_364_);
v___x_371_ = lean_int_dec_eq(v___x_370_, v___x_355_);
lean_dec(v___x_370_);
if (v___x_371_ == 0)
{
v___y_345_ = v___y_369_;
v___y_346_ = v___y_365_;
v___y_347_ = v___y_367_;
v___y_348_ = v___x_371_;
goto v___jp_344_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = lean_int_mod(v___y_367_, v___y_366_);
v___x_373_ = lean_int_dec_eq(v___x_372_, v___x_355_);
lean_dec(v___x_372_);
if (v___x_373_ == 0)
{
if (v___x_371_ == 0)
{
v___y_357_ = v___y_369_;
v___y_358_ = v___y_365_;
v___y_359_ = v___y_367_;
v___y_360_ = v___y_368_;
goto v___jp_356_;
}
else
{
v___y_345_ = v___y_369_;
v___y_346_ = v___y_365_;
v___y_347_ = v___y_367_;
v___y_348_ = v___x_371_;
goto v___jp_344_;
}
}
else
{
v___y_357_ = v___y_369_;
v___y_358_ = v___y_365_;
v___y_359_ = v___y_367_;
v___y_360_ = v___y_368_;
goto v___jp_356_;
}
}
}
v___jp_374_:
{
uint8_t v___x_382_; 
v___x_382_ = lean_int_dec_le(v___y_377_, v___y_375_);
if (v___x_382_ == 0)
{
lean_dec(v___y_375_);
lean_inc(v___y_377_);
v___y_364_ = v___y_376_;
v___y_365_ = v___y_381_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_379_;
v___y_368_ = v___y_380_;
v___y_369_ = v___y_377_;
goto v___jp_363_;
}
else
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__1, &l_Std_Time_PlainDate_ofEpochDay___closed__1_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__1);
v___x_384_ = lean_int_dec_le(v___y_375_, v___x_383_);
if (v___x_384_ == 0)
{
lean_dec(v___y_375_);
v___y_364_ = v___y_376_;
v___y_365_ = v___y_381_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_379_;
v___y_368_ = v___y_380_;
v___y_369_ = v___x_383_;
goto v___jp_363_;
}
else
{
v___y_364_ = v___y_376_;
v___y_365_ = v___y_381_;
v___y_366_ = v___y_378_;
v___y_367_ = v___y_379_;
v___y_368_ = v___y_380_;
v___y_369_ = v___y_375_;
goto v___jp_363_;
}
}
}
v___jp_385_:
{
lean_object* v_y_394_; uint8_t v___x_395_; 
v_y_394_ = lean_int_add(v___y_391_, v___y_393_);
lean_dec(v___y_391_);
v___x_395_ = lean_int_dec_le(v___y_388_, v___y_390_);
if (v___x_395_ == 0)
{
lean_dec(v___y_390_);
lean_inc(v___y_388_);
v___y_375_ = v___y_387_;
v___y_376_ = v___y_386_;
v___y_377_ = v___y_388_;
v___y_378_ = v___y_389_;
v___y_379_ = v_y_394_;
v___y_380_ = v___y_392_;
v___y_381_ = v___y_388_;
goto v___jp_374_;
}
else
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_397_ = lean_int_dec_le(v___y_390_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v___y_390_);
v___y_375_ = v___y_387_;
v___y_376_ = v___y_386_;
v___y_377_ = v___y_388_;
v___y_378_ = v___y_389_;
v___y_379_ = v_y_394_;
v___y_380_ = v___y_392_;
v___y_381_ = v___x_396_;
goto v___jp_374_;
}
else
{
v___y_375_ = v___y_387_;
v___y_376_ = v___y_386_;
v___y_377_ = v___y_388_;
v___y_378_ = v___y_389_;
v___y_379_ = v_y_394_;
v___y_380_ = v___y_392_;
v___y_381_ = v___y_390_;
goto v___jp_374_;
}
}
}
v___jp_398_:
{
lean_object* v_m_408_; uint8_t v___x_409_; 
v_m_408_ = lean_int_add(v___y_404_, v___y_407_);
lean_dec(v___y_404_);
v___x_409_ = lean_int_dec_le(v_m_408_, v___y_405_);
if (v___x_409_ == 0)
{
v___y_386_ = v___y_400_;
v___y_387_ = v___y_399_;
v___y_388_ = v___y_401_;
v___y_389_ = v___y_402_;
v___y_390_ = v_m_408_;
v___y_391_ = v___y_403_;
v___y_392_ = v___y_406_;
v___y_393_ = v___x_355_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___y_400_;
v___y_387_ = v___y_399_;
v___y_388_ = v___y_401_;
v___y_389_ = v___y_402_;
v___y_390_ = v_m_408_;
v___y_391_ = v___y_403_;
v___y_392_ = v___y_406_;
v___y_393_ = v___y_401_;
goto v___jp_385_;
}
}
v___jp_410_:
{
lean_object* v___x_412_; lean_object* v_era_413_; lean_object* v___x_414_; lean_object* v_doe_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v_yoe_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_y_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_doy_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_mp_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_d_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_412_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__3, &l_Std_Time_PlainDate_ofEpochDay___closed__3_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__3);
v_era_413_ = lean_int_div(v___y_411_, v___x_412_);
lean_dec(v___y_411_);
v___x_414_ = lean_int_mul(v_era_413_, v___x_412_);
v_doe_415_ = lean_int_sub(v_z_354_, v___x_414_);
lean_dec(v___x_414_);
lean_dec(v_z_354_);
v___x_416_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__4, &l_Std_Time_PlainDate_ofEpochDay___closed__4_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__4);
v___x_417_ = lean_int_div(v_doe_415_, v___x_416_);
v___x_418_ = lean_int_sub(v_doe_415_, v___x_417_);
lean_dec(v___x_417_);
v___x_419_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__5, &l_Std_Time_PlainDate_ofEpochDay___closed__5_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__5);
v___x_420_ = lean_int_div(v_doe_415_, v___x_419_);
v___x_421_ = lean_int_add(v___x_418_, v___x_420_);
lean_dec(v___x_420_);
lean_dec(v___x_418_);
v___x_422_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__6, &l_Std_Time_PlainDate_ofEpochDay___closed__6_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__6);
v___x_423_ = lean_int_div(v_doe_415_, v___x_422_);
v___x_424_ = lean_int_sub(v___x_421_, v___x_423_);
lean_dec(v___x_423_);
lean_dec(v___x_421_);
v___x_425_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__7, &l_Std_Time_PlainDate_ofEpochDay___closed__7_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__7);
v_yoe_426_ = lean_int_div(v___x_424_, v___x_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_428_ = lean_int_mul(v_era_413_, v___x_427_);
lean_dec(v_era_413_);
v_y_429_ = lean_int_add(v_yoe_426_, v___x_428_);
lean_dec(v___x_428_);
v___x_430_ = lean_int_mul(v___x_425_, v_yoe_426_);
v___x_431_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_432_ = lean_int_div(v_yoe_426_, v___x_431_);
v___x_433_ = lean_int_add(v___x_430_, v___x_432_);
lean_dec(v___x_432_);
lean_dec(v___x_430_);
v___x_434_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_435_ = lean_int_div(v_yoe_426_, v___x_434_);
lean_dec(v_yoe_426_);
v___x_436_ = lean_int_sub(v___x_433_, v___x_435_);
lean_dec(v___x_435_);
lean_dec(v___x_433_);
v_doy_437_ = lean_int_sub(v_doe_415_, v___x_436_);
lean_dec(v___x_436_);
lean_dec(v_doe_415_);
v___x_438_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_439_ = lean_int_mul(v___x_438_, v_doy_437_);
v___x_440_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__9, &l_Std_Time_PlainDate_ofEpochDay___closed__9_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__9);
v___x_441_ = lean_int_add(v___x_439_, v___x_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__10, &l_Std_Time_PlainDate_ofEpochDay___closed__10_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__10);
v_mp_443_ = lean_int_div(v___x_441_, v___x_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_int_mul(v___x_442_, v_mp_443_);
v___x_445_ = lean_int_add(v___x_444_, v___x_440_);
lean_dec(v___x_444_);
v___x_446_ = lean_int_div(v___x_445_, v___x_438_);
lean_dec(v___x_445_);
v___x_447_ = lean_int_sub(v_doy_437_, v___x_446_);
lean_dec(v___x_446_);
lean_dec(v_doy_437_);
v___x_448_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_d_449_ = lean_int_add(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__11, &l_Std_Time_PlainDate_ofEpochDay___closed__11_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__11);
v___x_451_ = lean_int_dec_lt(v_mp_443_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
v___x_452_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__12, &l_Std_Time_PlainDate_ofEpochDay___closed__12_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__12);
v___y_399_ = v_d_449_;
v___y_400_ = v___x_431_;
v___y_401_ = v___x_448_;
v___y_402_ = v___x_434_;
v___y_403_ = v_y_429_;
v___y_404_ = v_mp_443_;
v___y_405_ = v___x_440_;
v___y_406_ = v___x_427_;
v___y_407_ = v___x_452_;
goto v___jp_398_;
}
else
{
lean_object* v___x_453_; 
v___x_453_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___y_399_ = v_d_449_;
v___y_400_ = v___x_431_;
v___y_401_ = v___x_448_;
v___y_402_ = v___x_434_;
v___y_403_ = v_y_429_;
v___y_404_ = v_mp_443_;
v___y_405_ = v___x_440_;
v___y_406_ = v___x_427_;
v___y_407_ = v___x_453_;
goto v___jp_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofEpochDay___boxed(lean_object* v_day_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_Time_PlainDate_ofEpochDay(v_day_457_);
lean_dec(v_day_457_);
return v_res_458_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_460_ = lean_int_neg(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object* v_date_461_){
_start:
{
lean_object* v_day_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_day_462_ = lean_ctor_get(v_date_461_, 2);
v___x_463_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_464_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_465_ = lean_obj_once(&l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0, &l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0);
v___x_466_ = lean_int_add(v_day_462_, v___x_465_);
v___x_467_ = lean_int_ediv(v___x_466_, v___x_464_);
lean_dec(v___x_466_);
v___x_468_ = lean_int_add(v___x_467_, v___x_463_);
lean_dec(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth___boxed(lean_object* v_date_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_469_);
lean_dec_ref(v_date_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object* v_date_471_){
_start:
{
lean_object* v_month_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_month_472_ = lean_ctor_get(v_date_471_, 1);
v___x_473_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_474_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___x_475_ = lean_obj_once(&l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0, &l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0);
v___x_476_ = lean_int_add(v_month_472_, v___x_475_);
v___x_477_ = lean_int_ediv(v___x_476_, v___x_474_);
lean_dec(v___x_476_);
v___x_478_ = lean_int_add(v___x_477_, v___x_473_);
lean_dec(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object* v_date_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Time_PlainDate_quarter(v_date_479_);
lean_dec_ref(v_date_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object* v_date_481_){
_start:
{
lean_object* v_year_482_; lean_object* v_month_483_; lean_object* v_day_484_; uint8_t v___y_486_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_496_; 
v_year_482_ = lean_ctor_get(v_date_481_, 0);
v_month_483_ = lean_ctor_get(v_date_481_, 1);
v_day_484_ = lean_ctor_get(v_date_481_, 2);
v___x_489_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_490_ = lean_int_mod(v_year_482_, v___x_489_);
v___x_491_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_496_ = lean_int_dec_eq(v___x_490_, v___x_491_);
lean_dec(v___x_490_);
if (v___x_496_ == 0)
{
v___y_486_ = v___x_496_;
goto v___jp_485_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_498_ = lean_int_mod(v_year_482_, v___x_497_);
v___x_499_ = lean_int_dec_eq(v___x_498_, v___x_491_);
lean_dec(v___x_498_);
if (v___x_499_ == 0)
{
if (v___x_496_ == 0)
{
goto v___jp_492_;
}
else
{
v___y_486_ = v___x_496_;
goto v___jp_485_;
}
}
else
{
goto v___jp_492_;
}
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_day_484_);
lean_inc(v_month_483_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_month_483_);
lean_ctor_set(v___x_487_, 1, v_day_484_);
v___x_488_ = l_Std_Time_ValidDate_dayOfYear(v___y_486_, v___x_487_);
lean_dec_ref_known(v___x_487_, 2);
return v___x_488_;
}
v___jp_492_:
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_493_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_494_ = lean_int_mod(v_year_482_, v___x_493_);
v___x_495_ = lean_int_dec_eq(v___x_494_, v___x_491_);
lean_dec(v___x_494_);
v___y_486_ = v___x_495_;
goto v___jp_485_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object* v_date_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Std_Time_PlainDate_dayOfYear(v_date_500_);
lean_dec_ref(v_date_500_);
return v_res_501_;
}
}
uint8_t l_Std_Time_PlainDate_era(lean_object* v_date_502_){
_start:
{
lean_object* v_year_503_; uint8_t v___x_504_; 
v_year_503_ = lean_ctor_get(v_date_502_, 0);
v___x_504_ = l_Std_Time_Year_Offset_era(v_year_503_);
return v___x_504_;
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_era_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_502_ = stack[0].m_obj;
uint8_t v_res_505_;
v_res_505_ = l_Std_Time_PlainDate_era(v_date_502_);
stack->m_num = v_res_505_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object* v_date_506_){
_start:
{
uint8_t v_res_507_; lean_object* v_r_508_; 
v_res_507_ = l_Std_Time_PlainDate_era(v_date_506_);
lean_dec_ref(v_date_506_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object* v_date_509_){
_start:
{
lean_object* v_year_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_518_; 
v_year_510_ = lean_ctor_get(v_date_509_, 0);
v___x_511_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_512_ = lean_int_mod(v_year_510_, v___x_511_);
v___x_513_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_518_ = lean_int_dec_eq(v___x_512_, v___x_513_);
lean_dec(v___x_512_);
if (v___x_518_ == 0)
{
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_520_ = lean_int_mod(v_year_510_, v___x_519_);
v___x_521_ = lean_int_dec_eq(v___x_520_, v___x_513_);
lean_dec(v___x_520_);
if (v___x_521_ == 0)
{
if (v___x_518_ == 0)
{
goto v___jp_514_;
}
else
{
return v___x_518_;
}
}
else
{
goto v___jp_514_;
}
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_515_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_516_ = lean_int_mod(v_year_510_, v___x_515_);
v___x_517_ = lean_int_dec_eq(v___x_516_, v___x_513_);
lean_dec(v___x_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_inLeapYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_509_ = stack[0].m_obj;
uint8_t v_res_522_;
v_res_522_ = l_Std_Time_PlainDate_inLeapYear(v_date_509_);
stack->m_num = v_res_522_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object* v_date_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_Std_Time_PlainDate_inLeapYear(v_date_523_);
lean_dec_ref(v_date_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toEpochDay___closed__0(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___x_527_ = lean_int_neg(v___x_526_);
return v___x_527_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toEpochDay___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_unsigned_to_nat(399u);
v___x_529_ = lean_nat_to_int(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object* v_date_530_){
_start:
{
lean_object* v_year_531_; lean_object* v_month_532_; lean_object* v_day_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_574_; uint8_t v___x_579_; 
v_year_531_ = lean_ctor_get(v_date_530_, 0);
lean_inc(v_year_531_);
v_month_532_ = lean_ctor_get(v_date_530_, 1);
lean_inc(v_month_532_);
v_day_533_ = lean_ctor_get(v_date_530_, 2);
lean_inc(v_day_533_);
lean_dec_ref(v_date_530_);
v___x_534_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__9, &l_Std_Time_PlainDate_ofEpochDay___closed__9_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__9);
v___x_535_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_579_ = lean_int_dec_lt(v___x_534_, v_month_532_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_int_sub(v_year_531_, v___x_535_);
lean_dec(v_year_531_);
v___y_574_ = v___x_580_;
goto v___jp_573_;
}
else
{
v___y_574_ = v_year_531_;
goto v___jp_573_;
}
v___jp_536_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_doy_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_doe_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_541_ = lean_int_add(v_month_532_, v___y_540_);
lean_dec(v_month_532_);
v___x_542_ = lean_int_mul(v___y_539_, v___x_541_);
lean_dec(v___x_541_);
v___x_543_ = lean_int_add(v___x_542_, v___x_534_);
lean_dec(v___x_542_);
v___x_544_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_545_ = lean_int_div(v___x_543_, v___x_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_int_add(v___x_545_, v_day_533_);
lean_dec(v_day_533_);
lean_dec(v___x_545_);
v_doy_547_ = lean_int_sub(v___x_546_, v___x_535_);
lean_dec(v___x_546_);
v___x_548_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__7, &l_Std_Time_PlainDate_ofEpochDay___closed__7_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__7);
v___x_549_ = lean_int_mul(v___y_538_, v___x_548_);
v___x_550_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_551_ = lean_int_div(v___y_538_, v___x_550_);
v___x_552_ = lean_int_add(v___x_549_, v___x_551_);
lean_dec(v___x_551_);
lean_dec(v___x_549_);
v___x_553_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_554_ = lean_int_div(v___y_538_, v___x_553_);
lean_dec(v___y_538_);
v___x_555_ = lean_int_sub(v___x_552_, v___x_554_);
lean_dec(v___x_554_);
lean_dec(v___x_552_);
v_doe_556_ = lean_int_add(v___x_555_, v_doy_547_);
lean_dec(v_doy_547_);
lean_dec(v___x_555_);
v___x_557_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__3, &l_Std_Time_PlainDate_ofEpochDay___closed__3_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__3);
v___x_558_ = lean_int_mul(v___y_537_, v___x_557_);
lean_dec(v___y_537_);
v___x_559_ = lean_int_add(v___x_558_, v_doe_556_);
lean_dec(v_doe_556_);
lean_dec(v___x_558_);
v___x_560_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__0, &l_Std_Time_PlainDate_ofEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__0);
v___x_561_ = lean_int_sub(v___x_559_, v___x_560_);
lean_dec(v___x_559_);
return v___x_561_;
}
v___jp_562_:
{
lean_object* v___x_565_; lean_object* v_era_566_; lean_object* v___x_567_; lean_object* v_yoe_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_565_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v_era_566_ = lean_int_div(v___y_564_, v___x_565_);
lean_dec(v___y_564_);
v___x_567_ = lean_int_mul(v_era_566_, v___x_565_);
v_yoe_568_ = lean_int_sub(v___y_563_, v___x_567_);
lean_dec(v___x_567_);
lean_dec(v___y_563_);
v___x_569_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__10, &l_Std_Time_PlainDate_ofEpochDay___closed__10_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__10);
v___x_570_ = lean_int_dec_lt(v___x_534_, v_month_532_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___y_537_ = v_era_566_;
v___y_538_ = v_yoe_568_;
v___y_539_ = v___x_569_;
v___y_540_ = v___x_571_;
goto v___jp_536_;
}
else
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_Std_Time_PlainDate_toEpochDay___closed__0, &l_Std_Time_PlainDate_toEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_toEpochDay___closed__0);
v___y_537_ = v_era_566_;
v___y_538_ = v_yoe_568_;
v___y_539_ = v___x_569_;
v___y_540_ = v___x_572_;
goto v___jp_536_;
}
}
v___jp_573_:
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_576_ = lean_int_dec_le(v___x_575_, v___y_574_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_obj_once(&l_Std_Time_PlainDate_toEpochDay___closed__1, &l_Std_Time_PlainDate_toEpochDay___closed__1_once, _init_l_Std_Time_PlainDate_toEpochDay___closed__1);
v___x_578_ = lean_int_sub(v___y_574_, v___x_577_);
v___y_563_ = v___y_574_;
v___y_564_ = v___x_578_;
goto v___jp_562_;
}
else
{
lean_inc(v___y_574_);
v___y_563_ = v___y_574_;
v___y_564_ = v___y_574_;
goto v___jp_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays(lean_object* v_date_581_, lean_object* v_days_582_){
_start:
{
lean_object* v_dateDays_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_dateDays_583_ = l_Std_Time_PlainDate_toEpochDay(v_date_581_);
v___x_584_ = lean_int_add(v_dateDays_583_, v_days_582_);
lean_dec(v_dateDays_583_);
v___x_585_ = l_Std_Time_PlainDate_ofEpochDay(v___x_584_);
lean_dec(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays___boxed(lean_object* v_date_586_, lean_object* v_days_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_Time_PlainDate_addDays(v_date_586_, v_days_587_);
lean_dec(v_days_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays(lean_object* v_date_589_, lean_object* v_days_590_){
_start:
{
lean_object* v___x_591_; lean_object* v_dateDays_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_int_neg(v_days_590_);
v_dateDays_592_ = l_Std_Time_PlainDate_toEpochDay(v_date_589_);
v___x_593_ = lean_int_add(v_dateDays_592_, v___x_591_);
lean_dec(v___x_591_);
lean_dec(v_dateDays_592_);
v___x_594_ = l_Std_Time_PlainDate_ofEpochDay(v___x_593_);
lean_dec(v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays___boxed(lean_object* v_date_595_, lean_object* v_days_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_Time_PlainDate_subDays(v_date_595_, v_days_596_);
lean_dec(v_days_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks(lean_object* v_date_598_, lean_object* v_weeks_599_){
_start:
{
lean_object* v_dateDays_600_; lean_object* v___x_601_; lean_object* v_daysToAdd_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v_dateDays_600_ = l_Std_Time_PlainDate_toEpochDay(v_date_598_);
v___x_601_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_602_ = lean_int_mul(v_weeks_599_, v___x_601_);
v___x_603_ = lean_int_add(v_dateDays_600_, v_daysToAdd_602_);
lean_dec(v_daysToAdd_602_);
lean_dec(v_dateDays_600_);
v___x_604_ = l_Std_Time_PlainDate_ofEpochDay(v___x_603_);
lean_dec(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks___boxed(lean_object* v_date_605_, lean_object* v_weeks_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_Time_PlainDate_addWeeks(v_date_605_, v_weeks_606_);
lean_dec(v_weeks_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks(lean_object* v_date_608_, lean_object* v_weeks_609_){
_start:
{
lean_object* v___x_610_; lean_object* v_dateDays_611_; lean_object* v___x_612_; lean_object* v_daysToAdd_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_610_ = lean_int_neg(v_weeks_609_);
v_dateDays_611_ = l_Std_Time_PlainDate_toEpochDay(v_date_608_);
v___x_612_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_613_ = lean_int_mul(v___x_610_, v___x_612_);
lean_dec(v___x_610_);
v___x_614_ = lean_int_add(v_dateDays_611_, v_daysToAdd_613_);
lean_dec(v_daysToAdd_613_);
lean_dec(v_dateDays_611_);
v___x_615_ = l_Std_Time_PlainDate_ofEpochDay(v___x_614_);
lean_dec(v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks___boxed(lean_object* v_date_616_, lean_object* v_weeks_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_Time_PlainDate_subWeeks(v_date_616_, v_weeks_617_);
lean_dec(v_weeks_617_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object* v_date_619_, lean_object* v_months_620_){
_start:
{
lean_object* v_year_621_; lean_object* v_month_622_; lean_object* v_day_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_656_; 
v_year_621_ = lean_ctor_get(v_date_619_, 0);
v_month_622_ = lean_ctor_get(v_date_619_, 1);
v_day_623_ = lean_ctor_get(v_date_619_, 2);
v_isSharedCheck_656_ = !lean_is_exclusive(v_date_619_);
if (v_isSharedCheck_656_ == 0)
{
v___x_625_ = v_date_619_;
v_isShared_626_ = v_isSharedCheck_656_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_day_623_);
lean_inc(v_month_622_);
lean_inc(v_year_621_);
lean_dec(v_date_619_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_656_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_totalMonths_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_wrappedMonths_632_; lean_object* v_yearsOffset_633_; lean_object* v___x_634_; uint8_t v___y_636_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_652_; 
v___x_627_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_628_ = lean_int_sub(v_month_622_, v___x_627_);
lean_dec(v_month_622_);
v_totalMonths_629_ = lean_int_add(v___x_628_, v_months_620_);
lean_dec(v___x_628_);
v___x_630_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_631_ = lean_int_emod(v_totalMonths_629_, v___x_630_);
v_wrappedMonths_632_ = lean_int_add(v___x_631_, v___x_627_);
lean_dec(v___x_631_);
v_yearsOffset_633_ = lean_int_ediv(v_totalMonths_629_, v___x_630_);
lean_dec(v_totalMonths_629_);
v___x_634_ = lean_int_add(v_year_621_, v_yearsOffset_633_);
lean_dec(v_yearsOffset_633_);
lean_dec(v_year_621_);
v___x_645_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_646_ = lean_int_mod(v___x_634_, v___x_645_);
v___x_647_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_652_ = lean_int_dec_eq(v___x_646_, v___x_647_);
lean_dec(v___x_646_);
if (v___x_652_ == 0)
{
v___y_636_ = v___x_652_;
goto v___jp_635_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_654_ = lean_int_mod(v___x_634_, v___x_653_);
v___x_655_ = lean_int_dec_eq(v___x_654_, v___x_647_);
lean_dec(v___x_654_);
if (v___x_655_ == 0)
{
if (v___x_652_ == 0)
{
goto v___jp_648_;
}
else
{
v___y_636_ = v___x_652_;
goto v___jp_635_;
}
}
else
{
goto v___jp_648_;
}
}
v___jp_635_:
{
lean_object* v_max_637_; uint8_t v___x_638_; 
v_max_637_ = l_Std_Time_Month_Ordinal_days(v___y_636_, v_wrappedMonths_632_);
v___x_638_ = lean_int_dec_lt(v_max_637_, v_day_623_);
if (v___x_638_ == 0)
{
lean_object* v___x_640_; 
lean_dec(v_max_637_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_wrappedMonths_632_);
lean_ctor_set(v___x_625_, 0, v___x_634_);
v___x_640_ = v___x_625_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_wrappedMonths_632_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_day_623_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v_day_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 2, v_max_637_);
lean_ctor_set(v___x_625_, 1, v_wrappedMonths_632_);
lean_ctor_set(v___x_625_, 0, v___x_634_);
v___x_643_ = v___x_625_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_wrappedMonths_632_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_max_637_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
v___jp_648_:
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_650_ = lean_int_mod(v___x_634_, v___x_649_);
v___x_651_ = lean_int_dec_eq(v___x_650_, v___x_647_);
lean_dec(v___x_650_);
v___y_636_ = v___x_651_;
goto v___jp_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip___boxed(lean_object* v_date_657_, lean_object* v_months_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Time_PlainDate_addMonthsClip(v_date_657_, v_months_658_);
lean_dec(v_months_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip(lean_object* v_date_660_, lean_object* v_months_661_){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_int_neg(v_months_661_);
v___x_663_ = l_Std_Time_PlainDate_addMonthsClip(v_date_660_, v___x_662_);
lean_dec(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip___boxed(lean_object* v_date_664_, lean_object* v_months_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_Time_PlainDate_subMonthsClip(v_date_664_, v_months_665_);
lean_dec(v_months_665_);
return v_res_666_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__0(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(30u);
v___x_668_ = lean_nat_to_int(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__1(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__0, &l_Std_Time_PlainDate_rollOver___closed__0_once, _init_l_Std_Time_PlainDate_rollOver___closed__0);
v___x_670_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_671_ = lean_int_add(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__2(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_673_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__1, &l_Std_Time_PlainDate_rollOver___closed__1_once, _init_l_Std_Time_PlainDate_rollOver___closed__1);
v___x_674_ = lean_int_sub(v___x_673_, v___x_672_);
return v___x_674_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_range_677_; 
v___x_675_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_676_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__2, &l_Std_Time_PlainDate_rollOver___closed__2_once, _init_l_Std_Time_PlainDate_rollOver___closed__2);
v_range_677_ = lean_int_add(v___x_676_, v___x_675_);
return v_range_677_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__4(void){
_start:
{
lean_object* v_range_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_range_678_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_679_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_680_ = lean_int_emod(v___x_679_, v_range_678_);
return v___x_680_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__5(void){
_start:
{
lean_object* v_range_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_range_681_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_682_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__4, &l_Std_Time_PlainDate_rollOver___closed__4_once, _init_l_Std_Time_PlainDate_rollOver___closed__4);
v___x_683_ = lean_int_add(v___x_682_, v_range_681_);
return v___x_683_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__6(void){
_start:
{
lean_object* v_range_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_range_684_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_685_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__5, &l_Std_Time_PlainDate_rollOver___closed__5_once, _init_l_Std_Time_PlainDate_rollOver___closed__5);
v___x_686_ = lean_int_emod(v___x_685_, v_range_684_);
return v___x_686_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__7(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_688_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__6, &l_Std_Time_PlainDate_rollOver___closed__6_once, _init_l_Std_Time_PlainDate_rollOver___closed__6);
v___x_689_ = lean_int_add(v___x_688_, v___x_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver(lean_object* v_year_690_, lean_object* v_month_691_, lean_object* v_day_692_){
_start:
{
lean_object* v___y_694_; lean_object* v___x_700_; uint8_t v___y_702_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_714_; 
v___x_700_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_707_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_708_ = lean_int_mod(v_year_690_, v___x_707_);
v___x_709_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_714_ = lean_int_dec_eq(v___x_708_, v___x_709_);
lean_dec(v___x_708_);
if (v___x_714_ == 0)
{
v___y_702_ = v___x_714_;
goto v___jp_701_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_716_ = lean_int_mod(v_year_690_, v___x_715_);
v___x_717_ = lean_int_dec_eq(v___x_716_, v___x_709_);
lean_dec(v___x_716_);
if (v___x_717_ == 0)
{
if (v___x_714_ == 0)
{
goto v___jp_710_;
}
else
{
v___y_702_ = v___x_714_;
goto v___jp_701_;
}
}
else
{
goto v___jp_710_;
}
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_dateDays_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_695_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_696_ = lean_int_sub(v_day_692_, v___x_695_);
v_dateDays_697_ = l_Std_Time_PlainDate_toEpochDay(v___y_694_);
v___x_698_ = lean_int_add(v_dateDays_697_, v___x_696_);
lean_dec(v___x_696_);
lean_dec(v_dateDays_697_);
v___x_699_ = l_Std_Time_PlainDate_ofEpochDay(v___x_698_);
lean_dec(v___x_698_);
return v___x_699_;
}
v___jp_701_:
{
lean_object* v_max_703_; uint8_t v___x_704_; 
v_max_703_ = l_Std_Time_Month_Ordinal_days(v___y_702_, v_month_691_);
v___x_704_ = lean_int_dec_lt(v_max_703_, v___x_700_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; 
lean_dec(v_max_703_);
v___x_705_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_705_, 0, v_year_690_);
lean_ctor_set(v___x_705_, 1, v_month_691_);
lean_ctor_set(v___x_705_, 2, v___x_700_);
v___y_694_ = v___x_705_;
goto v___jp_693_;
}
else
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_706_, 0, v_year_690_);
lean_ctor_set(v___x_706_, 1, v_month_691_);
lean_ctor_set(v___x_706_, 2, v_max_703_);
v___y_694_ = v___x_706_;
goto v___jp_693_;
}
}
v___jp_710_:
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_712_ = lean_int_mod(v_year_690_, v___x_711_);
v___x_713_ = lean_int_dec_eq(v___x_712_, v___x_709_);
lean_dec(v___x_712_);
v___y_702_ = v___x_713_;
goto v___jp_701_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver___boxed(lean_object* v_year_718_, lean_object* v_month_719_, lean_object* v_day_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_Time_PlainDate_rollOver(v_year_718_, v_month_719_, v_day_720_);
lean_dec(v_day_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip(lean_object* v_dt_722_, lean_object* v_year_723_){
_start:
{
lean_object* v_month_724_; lean_object* v_day_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_750_; 
v_month_724_ = lean_ctor_get(v_dt_722_, 1);
v_day_725_ = lean_ctor_get(v_dt_722_, 2);
v_isSharedCheck_750_ = !lean_is_exclusive(v_dt_722_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v_dt_722_, 0);
lean_dec(v_unused_751_);
v___x_727_ = v_dt_722_;
v_isShared_728_ = v_isSharedCheck_750_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_day_725_);
lean_inc(v_month_724_);
lean_dec(v_dt_722_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_750_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
uint8_t v___y_730_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_746_; 
v___x_739_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_740_ = lean_int_mod(v_year_723_, v___x_739_);
v___x_741_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_746_ = lean_int_dec_eq(v___x_740_, v___x_741_);
lean_dec(v___x_740_);
if (v___x_746_ == 0)
{
v___y_730_ = v___x_746_;
goto v___jp_729_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_747_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_748_ = lean_int_mod(v_year_723_, v___x_747_);
v___x_749_ = lean_int_dec_eq(v___x_748_, v___x_741_);
lean_dec(v___x_748_);
if (v___x_749_ == 0)
{
if (v___x_746_ == 0)
{
goto v___jp_742_;
}
else
{
v___y_730_ = v___x_746_;
goto v___jp_729_;
}
}
else
{
goto v___jp_742_;
}
}
v___jp_729_:
{
lean_object* v_max_731_; uint8_t v___x_732_; 
v_max_731_ = l_Std_Time_Month_Ordinal_days(v___y_730_, v_month_724_);
v___x_732_ = lean_int_dec_lt(v_max_731_, v_day_725_);
if (v___x_732_ == 0)
{
lean_object* v___x_734_; 
lean_dec(v_max_731_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v_year_723_);
v___x_734_ = v___x_727_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_year_723_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_month_724_);
lean_ctor_set(v_reuseFailAlloc_735_, 2, v_day_725_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
else
{
lean_object* v___x_737_; 
lean_dec(v_day_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 2, v_max_731_);
lean_ctor_set(v___x_727_, 0, v_year_723_);
v___x_737_ = v___x_727_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_year_723_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_month_724_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_max_731_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
v___jp_742_:
{
lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_744_ = lean_int_mod(v_year_723_, v___x_743_);
v___x_745_ = lean_int_dec_eq(v___x_744_, v___x_741_);
lean_dec(v___x_744_);
v___y_730_ = v___x_745_;
goto v___jp_729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearRollOver(lean_object* v_dt_752_, lean_object* v_year_753_){
_start:
{
lean_object* v_month_754_; lean_object* v_day_755_; lean_object* v___x_756_; 
v_month_754_ = lean_ctor_get(v_dt_752_, 1);
lean_inc(v_month_754_);
v_day_755_ = lean_ctor_get(v_dt_752_, 2);
lean_inc(v_day_755_);
lean_dec_ref(v_dt_752_);
v___x_756_ = l_Std_Time_PlainDate_rollOver(v_year_753_, v_month_754_, v_day_755_);
lean_dec(v_day_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object* v_date_757_, lean_object* v_months_758_){
_start:
{
lean_object* v_year_759_; lean_object* v_month_760_; lean_object* v_day_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_795_; 
v_year_759_ = lean_ctor_get(v_date_757_, 0);
v_month_760_ = lean_ctor_get(v_date_757_, 1);
v_day_761_ = lean_ctor_get(v_date_757_, 2);
v_isSharedCheck_795_ = !lean_is_exclusive(v_date_757_);
if (v_isSharedCheck_795_ == 0)
{
v___x_763_ = v_date_757_;
v_isShared_764_ = v_isSharedCheck_795_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_day_761_);
lean_inc(v_month_760_);
lean_inc(v_year_759_);
lean_dec(v_date_757_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_795_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___y_766_; lean_object* v___x_773_; uint8_t v___y_775_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_791_; 
v___x_773_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_784_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_785_ = lean_int_mod(v_year_759_, v___x_784_);
v___x_786_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_791_ = lean_int_dec_eq(v___x_785_, v___x_786_);
lean_dec(v___x_785_);
if (v___x_791_ == 0)
{
v___y_775_ = v___x_791_;
goto v___jp_774_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_793_ = lean_int_mod(v_year_759_, v___x_792_);
v___x_794_ = lean_int_dec_eq(v___x_793_, v___x_786_);
lean_dec(v___x_793_);
if (v___x_794_ == 0)
{
if (v___x_791_ == 0)
{
goto v___jp_787_;
}
else
{
v___y_775_ = v___x_791_;
goto v___jp_774_;
}
}
else
{
goto v___jp_787_;
}
}
v___jp_765_:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_dateDays_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_767_ = l_Std_Time_PlainDate_addMonthsClip(v___y_766_, v_months_758_);
v___x_768_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_769_ = lean_int_sub(v_day_761_, v___x_768_);
lean_dec(v_day_761_);
v_dateDays_770_ = l_Std_Time_PlainDate_toEpochDay(v___x_767_);
v___x_771_ = lean_int_add(v_dateDays_770_, v___x_769_);
lean_dec(v___x_769_);
lean_dec(v_dateDays_770_);
v___x_772_ = l_Std_Time_PlainDate_ofEpochDay(v___x_771_);
lean_dec(v___x_771_);
return v___x_772_;
}
v___jp_774_:
{
lean_object* v_max_776_; uint8_t v___x_777_; 
v_max_776_ = l_Std_Time_Month_Ordinal_days(v___y_775_, v_month_760_);
v___x_777_ = lean_int_dec_lt(v_max_776_, v___x_773_);
if (v___x_777_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v_max_776_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v___x_773_);
v___x_779_ = v___x_763_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_year_759_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_month_760_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v___x_773_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
v___y_766_ = v___x_779_;
goto v___jp_765_;
}
}
else
{
lean_object* v___x_782_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v_max_776_);
v___x_782_ = v___x_763_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_year_759_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_month_760_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_max_776_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
v___y_766_ = v___x_782_;
goto v___jp_765_;
}
}
}
v___jp_787_:
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_789_ = lean_int_mod(v_year_759_, v___x_788_);
v___x_790_ = lean_int_dec_eq(v___x_789_, v___x_786_);
lean_dec(v___x_789_);
v___y_775_ = v___x_790_;
goto v___jp_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver___boxed(lean_object* v_date_796_, lean_object* v_months_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_796_, v_months_797_);
lean_dec(v_months_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver(lean_object* v_date_799_, lean_object* v_months_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_int_neg(v_months_800_);
v___x_802_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_799_, v___x_801_);
lean_dec(v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver___boxed(lean_object* v_date_803_, lean_object* v_months_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_Time_PlainDate_subMonthsRollOver(v_date_803_, v_months_804_);
lean_dec(v_months_804_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver(lean_object* v_date_806_, lean_object* v_years_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_809_ = lean_int_mul(v_years_807_, v___x_808_);
v___x_810_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_806_, v___x_809_);
lean_dec(v___x_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver___boxed(lean_object* v_date_811_, lean_object* v_years_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_Time_PlainDate_addYearsRollOver(v_date_811_, v_years_812_);
lean_dec(v_years_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver(lean_object* v_date_814_, lean_object* v_years_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_816_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_817_ = lean_int_mul(v_years_815_, v___x_816_);
v___x_818_ = lean_int_neg(v___x_817_);
lean_dec(v___x_817_);
v___x_819_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_814_, v___x_818_);
lean_dec(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver___boxed(lean_object* v_date_820_, lean_object* v_years_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_Time_PlainDate_subYearsRollOver(v_date_820_, v_years_821_);
lean_dec(v_years_821_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip(lean_object* v_date_823_, lean_object* v_years_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_826_ = lean_int_mul(v_years_824_, v___x_825_);
v___x_827_ = l_Std_Time_PlainDate_addMonthsClip(v_date_823_, v___x_826_);
lean_dec(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip___boxed(lean_object* v_date_828_, lean_object* v_years_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_Time_PlainDate_addYearsClip(v_date_828_, v_years_829_);
lean_dec(v_years_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip(lean_object* v_date_831_, lean_object* v_years_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_833_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_834_ = lean_int_mul(v_years_832_, v___x_833_);
v___x_835_ = lean_int_neg(v___x_834_);
lean_dec(v___x_834_);
v___x_836_ = l_Std_Time_PlainDate_addMonthsClip(v_date_831_, v___x_835_);
lean_dec(v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip___boxed(lean_object* v_date_837_, lean_object* v_years_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_Time_PlainDate_subYearsClip(v_date_837_, v_years_838_);
lean_dec(v_years_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip(lean_object* v_dt_840_, lean_object* v_days_841_){
_start:
{
lean_object* v_year_842_; lean_object* v_month_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_868_; 
v_year_842_ = lean_ctor_get(v_dt_840_, 0);
v_month_843_ = lean_ctor_get(v_dt_840_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_dt_840_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v_dt_840_, 2);
lean_dec(v_unused_869_);
v___x_845_ = v_dt_840_;
v_isShared_846_ = v_isSharedCheck_868_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_month_843_);
lean_inc(v_year_842_);
lean_dec(v_dt_840_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_868_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___y_848_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_864_; 
v___x_857_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_858_ = lean_int_mod(v_year_842_, v___x_857_);
v___x_859_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_864_ = lean_int_dec_eq(v___x_858_, v___x_859_);
lean_dec(v___x_858_);
if (v___x_864_ == 0)
{
v___y_848_ = v___x_864_;
goto v___jp_847_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_865_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_866_ = lean_int_mod(v_year_842_, v___x_865_);
v___x_867_ = lean_int_dec_eq(v___x_866_, v___x_859_);
lean_dec(v___x_866_);
if (v___x_867_ == 0)
{
if (v___x_864_ == 0)
{
goto v___jp_860_;
}
else
{
v___y_848_ = v___x_864_;
goto v___jp_847_;
}
}
else
{
goto v___jp_860_;
}
}
v___jp_847_:
{
lean_object* v_max_849_; uint8_t v___x_850_; 
v_max_849_ = l_Std_Time_Month_Ordinal_days(v___y_848_, v_month_843_);
v___x_850_ = lean_int_dec_lt(v_max_849_, v_days_841_);
if (v___x_850_ == 0)
{
lean_object* v___x_852_; 
lean_dec(v_max_849_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 2, v_days_841_);
v___x_852_ = v___x_845_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_year_842_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_month_843_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_days_841_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
else
{
lean_object* v___x_855_; 
lean_dec(v_days_841_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 2, v_max_849_);
v___x_855_ = v___x_845_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_year_842_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_month_843_);
lean_ctor_set(v_reuseFailAlloc_856_, 2, v_max_849_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
v___jp_860_:
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_862_ = lean_int_mod(v_year_842_, v___x_861_);
v___x_863_ = lean_int_dec_eq(v___x_862_, v___x_859_);
lean_dec(v___x_862_);
v___y_848_ = v___x_863_;
goto v___jp_847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver(lean_object* v_dt_870_, lean_object* v_days_871_){
_start:
{
lean_object* v_year_872_; lean_object* v_month_873_; lean_object* v___x_874_; 
v_year_872_ = lean_ctor_get(v_dt_870_, 0);
lean_inc(v_year_872_);
v_month_873_ = lean_ctor_get(v_dt_870_, 1);
lean_inc(v_month_873_);
lean_dec_ref(v_dt_870_);
v___x_874_ = l_Std_Time_PlainDate_rollOver(v_year_872_, v_month_873_, v_days_871_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver___boxed(lean_object* v_dt_875_, lean_object* v_days_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Time_PlainDate_withDaysRollOver(v_dt_875_, v_days_876_);
lean_dec(v_days_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip(lean_object* v_dt_878_, lean_object* v_month_879_){
_start:
{
lean_object* v_year_880_; lean_object* v_day_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_906_; 
v_year_880_ = lean_ctor_get(v_dt_878_, 0);
v_day_881_ = lean_ctor_get(v_dt_878_, 2);
v_isSharedCheck_906_ = !lean_is_exclusive(v_dt_878_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; 
v_unused_907_ = lean_ctor_get(v_dt_878_, 1);
lean_dec(v_unused_907_);
v___x_883_ = v_dt_878_;
v_isShared_884_ = v_isSharedCheck_906_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_day_881_);
lean_inc(v_year_880_);
lean_dec(v_dt_878_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_906_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v___y_886_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_902_; 
v___x_895_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_896_ = lean_int_mod(v_year_880_, v___x_895_);
v___x_897_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_902_ = lean_int_dec_eq(v___x_896_, v___x_897_);
lean_dec(v___x_896_);
if (v___x_902_ == 0)
{
v___y_886_ = v___x_902_;
goto v___jp_885_;
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_904_ = lean_int_mod(v_year_880_, v___x_903_);
v___x_905_ = lean_int_dec_eq(v___x_904_, v___x_897_);
lean_dec(v___x_904_);
if (v___x_905_ == 0)
{
if (v___x_902_ == 0)
{
goto v___jp_898_;
}
else
{
v___y_886_ = v___x_902_;
goto v___jp_885_;
}
}
else
{
goto v___jp_898_;
}
}
v___jp_885_:
{
lean_object* v_max_887_; uint8_t v___x_888_; 
v_max_887_ = l_Std_Time_Month_Ordinal_days(v___y_886_, v_month_879_);
v___x_888_ = lean_int_dec_lt(v_max_887_, v_day_881_);
if (v___x_888_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_max_887_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v_month_879_);
v___x_890_ = v___x_883_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_year_880_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_month_879_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_day_881_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
lean_object* v___x_893_; 
lean_dec(v_day_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 2, v_max_887_);
lean_ctor_set(v___x_883_, 1, v_month_879_);
v___x_893_ = v___x_883_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_year_880_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_month_879_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_max_887_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
v___jp_898_:
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_899_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_900_ = lean_int_mod(v_year_880_, v___x_899_);
v___x_901_ = lean_int_dec_eq(v___x_900_, v___x_897_);
lean_dec(v___x_900_);
v___y_886_ = v___x_901_;
goto v___jp_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthRollOver(lean_object* v_dt_908_, lean_object* v_month_909_){
_start:
{
lean_object* v_year_910_; lean_object* v_day_911_; lean_object* v___x_912_; 
v_year_910_ = lean_ctor_get(v_dt_908_, 0);
lean_inc(v_year_910_);
v_day_911_ = lean_ctor_get(v_dt_908_, 2);
lean_inc(v_day_911_);
lean_dec_ref(v_dt_908_);
v___x_912_ = l_Std_Time_PlainDate_rollOver(v_year_910_, v_month_909_, v_day_911_);
lean_dec(v_day_911_);
return v___x_912_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_914_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_915_ = lean_int_sub(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_range_918_; 
v___x_916_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_917_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__0, &l_Std_Time_PlainDate_weekday___closed__0_once, _init_l_Std_Time_PlainDate_weekday___closed__0);
v_range_918_ = lean_int_add(v___x_917_, v___x_916_);
return v_range_918_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__2(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_920_ = lean_int_neg(v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__3(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_unsigned_to_nat(6u);
v___x_922_ = lean_nat_to_int(v___x_921_);
return v___x_922_;
}
}
uint8_t l_Std_Time_PlainDate_weekday(lean_object* v_date_923_){
_start:
{
lean_object* v___y_925_; lean_object* v_days_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_days_934_ = l_Std_Time_PlainDate_toEpochDay(v_date_923_);
v___x_935_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_936_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__2, &l_Std_Time_PlainDate_weekday___closed__2_once, _init_l_Std_Time_PlainDate_weekday___closed__2);
v___x_937_ = lean_int_dec_le(v___x_936_, v_days_934_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_938_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_939_ = lean_int_add(v_days_934_, v___x_938_);
lean_dec(v_days_934_);
v___x_940_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_941_ = lean_int_emod(v___x_939_, v___x_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__3, &l_Std_Time_PlainDate_weekday___closed__3_once, _init_l_Std_Time_PlainDate_weekday___closed__3);
v___x_943_ = lean_int_add(v___x_941_, v___x_942_);
lean_dec(v___x_941_);
v___y_925_ = v___x_943_;
goto v___jp_924_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_int_add(v_days_934_, v___x_935_);
lean_dec(v_days_934_);
v___x_945_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_946_ = lean_int_emod(v___x_944_, v___x_945_);
lean_dec(v___x_944_);
v___y_925_ = v___x_946_;
goto v___jp_924_;
}
v___jp_924_:
{
lean_object* v___x_926_; lean_object* v_range_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_926_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_range_927_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__1, &l_Std_Time_PlainDate_weekday___closed__1_once, _init_l_Std_Time_PlainDate_weekday___closed__1);
v___x_928_ = lean_int_sub(v___y_925_, v___x_926_);
lean_dec(v___y_925_);
v___x_929_ = lean_int_emod(v___x_928_, v_range_927_);
lean_dec(v___x_928_);
v___x_930_ = lean_int_add(v___x_929_, v_range_927_);
lean_dec(v___x_929_);
v___x_931_ = lean_int_emod(v___x_930_, v_range_927_);
lean_dec(v___x_930_);
v___x_932_ = lean_int_add(v___x_931_, v___x_926_);
lean_dec(v___x_931_);
v___x_933_ = l_Std_Time_Weekday_ofOrdinal(v___x_932_);
lean_dec(v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_weekday_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_923_ = stack[0].m_obj;
uint8_t v_res_947_;
v_res_947_ = l_Std_Time_PlainDate_weekday(v_date_923_);
stack->m_num = v_res_947_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekday___boxed(lean_object* v_date_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Std_Time_PlainDate_weekday(v_date_948_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfMonth___closed__0(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_952_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__3, &l_Std_Time_PlainDate_weekday___closed__3_once, _init_l_Std_Time_PlainDate_weekday___closed__3);
v___x_953_ = lean_int_sub(v___x_952_, v___x_951_);
return v___x_953_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfMonth___closed__1(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_range_956_; 
v___x_954_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_955_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v_range_956_ = lean_int_add(v___x_955_, v___x_954_);
return v_range_956_;
}
}
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object* v_date_957_, uint8_t v_firstDay_958_){
_start:
{
lean_object* v_year_959_; lean_object* v_month_960_; lean_object* v_day_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1007_; 
v_year_959_ = lean_ctor_get(v_date_957_, 0);
v_month_960_ = lean_ctor_get(v_date_957_, 1);
v_day_961_ = lean_ctor_get(v_date_957_, 2);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_date_957_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_963_ = v_date_957_;
v_isShared_964_ = v_isSharedCheck_1007_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_day_961_);
lean_inc(v_month_960_);
lean_inc(v_year_959_);
lean_dec(v_date_957_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1007_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___y_966_; lean_object* v___x_985_; uint8_t v___y_987_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_1003_; 
v___x_985_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_996_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_997_ = lean_int_mod(v_year_959_, v___x_996_);
v___x_998_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1003_ = lean_int_dec_eq(v___x_997_, v___x_998_);
lean_dec(v___x_997_);
if (v___x_1003_ == 0)
{
v___y_987_ = v___x_1003_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_1005_ = lean_int_mod(v_year_959_, v___x_1004_);
v___x_1006_ = lean_int_dec_eq(v___x_1005_, v___x_998_);
lean_dec(v___x_1005_);
if (v___x_1006_ == 0)
{
if (v___x_1003_ == 0)
{
goto v___jp_999_;
}
else
{
v___y_987_ = v___x_1003_;
goto v___jp_986_;
}
}
else
{
goto v___jp_999_;
}
}
v___jp_965_:
{
uint8_t v___x_967_; lean_object* v_day1Ord_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_offset_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v_range_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_967_ = l_Std_Time_PlainDate_weekday(v___y_966_);
v_day1Ord_968_ = l_Std_Time_Weekday_toOrdinal(v___x_967_);
v___x_969_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_958_);
v___x_970_ = lean_int_sub(v_day1Ord_968_, v___x_969_);
lean_dec(v___x_969_);
lean_dec(v_day1Ord_968_);
v___x_971_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_972_ = lean_int_add(v___x_970_, v___x_971_);
lean_dec(v___x_970_);
v_offset_973_ = lean_int_emod(v___x_972_, v___x_971_);
lean_dec(v___x_972_);
v___x_974_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_975_ = lean_int_sub(v_day_961_, v___x_974_);
lean_dec(v_day_961_);
v___x_976_ = lean_int_add(v___x_975_, v_offset_973_);
lean_dec(v_offset_973_);
lean_dec(v___x_975_);
v___x_977_ = lean_int_ediv(v___x_976_, v___x_971_);
lean_dec(v___x_976_);
v___x_978_ = lean_int_add(v___x_977_, v___x_974_);
lean_dec(v___x_977_);
v_range_979_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__1, &l_Std_Time_PlainDate_weekOfMonth___closed__1_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__1);
v___x_980_ = lean_int_sub(v___x_978_, v___x_974_);
lean_dec(v___x_978_);
v___x_981_ = lean_int_emod(v___x_980_, v_range_979_);
lean_dec(v___x_980_);
v___x_982_ = lean_int_add(v___x_981_, v_range_979_);
lean_dec(v___x_981_);
v___x_983_ = lean_int_emod(v___x_982_, v_range_979_);
lean_dec(v___x_982_);
v___x_984_ = lean_int_add(v___x_983_, v___x_974_);
lean_dec(v___x_983_);
return v___x_984_;
}
v___jp_986_:
{
lean_object* v_max_988_; uint8_t v___x_989_; 
v_max_988_ = l_Std_Time_Month_Ordinal_days(v___y_987_, v_month_960_);
v___x_989_ = lean_int_dec_lt(v_max_988_, v___x_985_);
if (v___x_989_ == 0)
{
lean_object* v___x_991_; 
lean_dec(v_max_988_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 2, v___x_985_);
v___x_991_ = v___x_963_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_year_959_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_month_960_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v___x_985_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v___y_966_ = v___x_991_;
goto v___jp_965_;
}
}
else
{
lean_object* v___x_994_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 2, v_max_988_);
v___x_994_ = v___x_963_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_year_959_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_month_960_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_max_988_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
v___y_966_ = v___x_994_;
goto v___jp_965_;
}
}
}
v___jp_999_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1000_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_1001_ = lean_int_mod(v_year_959_, v___x_1000_);
v___x_1002_ = lean_int_dec_eq(v___x_1001_, v___x_998_);
lean_dec(v___x_1001_);
v___y_987_ = v___x_1002_;
goto v___jp_986_;
}
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_weekOfMonth_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_957_ = stack[0].m_obj;
uint8_t v_firstDay_958_ = stack[1].m_num;
lean_object* v_res_1008_;
v_res_1008_ = l_Std_Time_PlainDate_weekOfMonth(v_date_957_, v_firstDay_958_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object* v_date_1009_, lean_object* v_firstDay_1010_){
_start:
{
uint8_t v_firstDay_boxed_1011_; lean_object* v_res_1012_; 
v_firstDay_boxed_1011_ = lean_unbox(v_firstDay_1010_);
v_res_1012_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1009_, v_firstDay_boxed_1011_);
return v_res_1012_;
}
}
lean_object* l_Std_Time_PlainDate_withWeekday(lean_object* v_date_1013_, uint8_t v_desiredWeekday_1014_){
_start:
{
lean_object* v___y_1016_; uint8_t v___x_1020_; lean_object* v_weekday_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
lean_inc_ref(v_date_1013_);
v___x_1020_ = l_Std_Time_PlainDate_weekday(v_date_1013_);
v_weekday_1021_ = l_Std_Time_Weekday_toOrdinal(v___x_1020_);
v___x_1022_ = l_Std_Time_Weekday_toOrdinal(v_desiredWeekday_1014_);
v___x_1023_ = lean_int_neg(v_weekday_1021_);
lean_dec(v_weekday_1021_);
v___x_1024_ = lean_int_add(v___x_1022_, v___x_1023_);
lean_dec(v___x_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1026_ = lean_int_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
v___y_1016_ = v___x_1024_;
goto v___jp_1015_;
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1028_ = lean_int_add(v___x_1024_, v___x_1027_);
lean_dec(v___x_1024_);
v___y_1016_ = v___x_1028_;
goto v___jp_1015_;
}
v___jp_1015_:
{
lean_object* v_dateDays_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_dateDays_1017_ = l_Std_Time_PlainDate_toEpochDay(v_date_1013_);
v___x_1018_ = lean_int_add(v_dateDays_1017_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec(v_dateDays_1017_);
v___x_1019_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1018_);
lean_dec(v___x_1018_);
return v___x_1019_;
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_withWeekday_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1013_ = stack[0].m_obj;
uint8_t v_desiredWeekday_1014_ = stack[1].m_num;
lean_object* v_res_1029_;
v_res_1029_ = l_Std_Time_PlainDate_withWeekday(v_date_1013_, v_desiredWeekday_1014_);
stack->m_obj
 = v_res_1029_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object* v_date_1030_, lean_object* v_desiredWeekday_1031_){
_start:
{
uint8_t v_desiredWeekday_boxed_1032_; lean_object* v_res_1033_; 
v_desiredWeekday_boxed_1032_ = lean_unbox(v_desiredWeekday_1031_);
v_res_1033_ = l_Std_Time_PlainDate_withWeekday(v_date_1030_, v_desiredWeekday_boxed_1032_);
return v_res_1033_;
}
}
lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(uint8_t v_weekday_1034_, uint8_t v_firstDay_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1036_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1037_ = l_Std_Time_Weekday_toOrdinal(v_weekday_1034_);
v___x_1038_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_1035_);
v___x_1039_ = lean_int_neg(v___x_1038_);
lean_dec(v___x_1038_);
v___x_1040_ = lean_int_add(v___x_1037_, v___x_1039_);
lean_dec(v___x_1039_);
lean_dec(v___x_1037_);
v___x_1041_ = lean_int_emod(v___x_1040_, v___x_1036_);
lean_dec(v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT void l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek_0interp(lean_interpreter_value* stack)
{
uint8_t v_weekday_1034_ = stack[0].m_num;
uint8_t v_firstDay_1035_ = stack[1].m_num;
lean_object* v_res_1042_;
v_res_1042_ = l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(v_weekday_1034_, v_firstDay_1035_);
stack->m_obj
 = v_res_1042_;
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek___boxed(lean_object* v_weekday_1043_, lean_object* v_firstDay_1044_){
_start:
{
uint8_t v_weekday_boxed_1045_; uint8_t v_firstDay_boxed_1046_; lean_object* v_res_1047_; 
v_weekday_boxed_1045_ = lean_unbox(v_weekday_1043_);
v_firstDay_boxed_1046_ = lean_unbox(v_firstDay_1044_);
v_res_1047_ = l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(v_weekday_boxed_1045_, v_firstDay_boxed_1046_);
return v_res_1047_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = lean_unsigned_to_nat(11u);
v___x_1049_ = lean_nat_to_int(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0);
v___x_1051_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1052_ = lean_int_add(v___x_1051_, v___x_1050_);
return v___x_1052_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1054_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1);
v___x_1055_ = lean_int_sub(v___x_1054_, v___x_1053_);
return v___x_1055_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_range_1058_; 
v___x_1056_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1057_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2);
v_range_1058_ = lean_int_add(v___x_1057_, v___x_1056_);
return v_range_1058_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4(void){
_start:
{
lean_object* v_range_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_range_1059_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1060_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_1061_ = lean_int_emod(v___x_1060_, v_range_1059_);
return v___x_1061_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5(void){
_start:
{
lean_object* v_range_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_range_1062_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1063_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4);
v___x_1064_ = lean_int_add(v___x_1063_, v_range_1062_);
return v___x_1064_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6(void){
_start:
{
lean_object* v_range_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_range_1065_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1066_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5);
v___x_1067_ = lean_int_emod(v___x_1066_, v_range_1065_);
return v___x_1067_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1069_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6);
v___x_1070_ = lean_int_add(v___x_1069_, v___x_1068_);
return v___x_1070_;
}
}
lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear(lean_object* v_year_1071_, uint8_t v_firstDay_1072_, lean_object* v_minimalDays_1073_){
_start:
{
lean_object* v___y_1075_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___y_1094_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1106_; 
v___x_1091_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7);
v___x_1092_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_1099_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_1100_ = lean_int_mod(v_year_1071_, v___x_1099_);
v___x_1101_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1106_ = lean_int_dec_eq(v___x_1100_, v___x_1101_);
lean_dec(v___x_1100_);
if (v___x_1106_ == 0)
{
v___y_1094_ = v___x_1106_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1107_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_1108_ = lean_int_mod(v_year_1071_, v___x_1107_);
v___x_1109_ = lean_int_dec_eq(v___x_1108_, v___x_1101_);
lean_dec(v___x_1108_);
if (v___x_1109_ == 0)
{
if (v___x_1106_ == 0)
{
goto v___jp_1102_;
}
else
{
v___y_1094_ = v___x_1106_;
goto v___jp_1093_;
}
}
else
{
goto v___jp_1102_;
}
}
v___jp_1074_:
{
uint8_t v___x_1076_; lean_object* v_localDay_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_dateDays_1084_; lean_object* v___x_1085_; lean_object* v_weekStart_1086_; uint8_t v___x_1087_; 
lean_inc_ref(v___y_1075_);
v___x_1076_ = l_Std_Time_PlainDate_weekday(v___y_1075_);
v_localDay_1077_ = l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(v___x_1076_, v_firstDay_1072_);
v___x_1078_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1079_ = lean_int_neg(v_localDay_1077_);
v___x_1080_ = lean_int_add(v___x_1078_, v___x_1079_);
lean_dec(v___x_1079_);
v___x_1081_ = l_Int_toNat(v_localDay_1077_);
lean_dec(v_localDay_1077_);
v___x_1082_ = lean_nat_to_int(v___x_1081_);
v___x_1083_ = lean_int_neg(v___x_1082_);
lean_dec(v___x_1082_);
v_dateDays_1084_ = l_Std_Time_PlainDate_toEpochDay(v___y_1075_);
v___x_1085_ = lean_int_add(v_dateDays_1084_, v___x_1083_);
lean_dec(v___x_1083_);
lean_dec(v_dateDays_1084_);
v_weekStart_1086_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1085_);
lean_dec(v___x_1085_);
v___x_1087_ = lean_int_dec_le(v_minimalDays_1073_, v___x_1080_);
lean_dec(v___x_1080_);
if (v___x_1087_ == 0)
{
lean_object* v_dateDays_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_dateDays_1088_ = l_Std_Time_PlainDate_toEpochDay(v_weekStart_1086_);
v___x_1089_ = lean_int_add(v_dateDays_1088_, v___x_1078_);
lean_dec(v_dateDays_1088_);
v___x_1090_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1089_);
lean_dec(v___x_1089_);
return v___x_1090_;
}
else
{
return v_weekStart_1086_;
}
}
v___jp_1093_:
{
lean_object* v_max_1095_; uint8_t v___x_1096_; 
v_max_1095_ = l_Std_Time_Month_Ordinal_days(v___y_1094_, v___x_1091_);
v___x_1096_ = lean_int_dec_lt(v_max_1095_, v___x_1092_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v_max_1095_);
v___x_1097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1097_, 0, v_year_1071_);
lean_ctor_set(v___x_1097_, 1, v___x_1091_);
lean_ctor_set(v___x_1097_, 2, v___x_1092_);
v___y_1075_ = v___x_1097_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1098_, 0, v_year_1071_);
lean_ctor_set(v___x_1098_, 1, v___x_1091_);
lean_ctor_set(v___x_1098_, 2, v_max_1095_);
v___y_1075_ = v___x_1098_;
goto v___jp_1074_;
}
}
v___jp_1102_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_1104_ = lean_int_mod(v_year_1071_, v___x_1103_);
v___x_1105_ = lean_int_dec_eq(v___x_1104_, v___x_1101_);
lean_dec(v___x_1104_);
v___y_1094_ = v___x_1105_;
goto v___jp_1093_;
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_startOfWeekBasedYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_year_1071_ = stack[0].m_obj;
uint8_t v_firstDay_1072_ = stack[1].m_num;
lean_object* v_minimalDays_1073_ = stack[2].m_obj;
lean_object* v_res_1110_;
v_res_1110_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1071_, v_firstDay_1072_, v_minimalDays_1073_);
stack->m_obj
 = v_res_1110_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___boxed(lean_object* v_year_1111_, lean_object* v_firstDay_1112_, lean_object* v_minimalDays_1113_){
_start:
{
uint8_t v_firstDay_boxed_1114_; lean_object* v_res_1115_; 
v_firstDay_boxed_1114_ = lean_unbox(v_firstDay_1112_);
v_res_1115_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1111_, v_firstDay_boxed_1114_, v_minimalDays_1113_);
lean_dec(v_minimalDays_1113_);
return v_res_1115_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__0(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_unsigned_to_nat(370u);
v___x_1117_ = lean_nat_to_int(v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__1(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1119_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__0, &l_Std_Time_PlainDate_weekOfYear___closed__0_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__0);
v___x_1120_ = lean_int_sub(v___x_1119_, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__2(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_range_1123_; 
v___x_1121_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1122_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__1, &l_Std_Time_PlainDate_weekOfYear___closed__1_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__1);
v_range_1123_ = lean_int_add(v___x_1122_, v___x_1121_);
return v_range_1123_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__3(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = lean_unsigned_to_nat(52u);
v___x_1125_ = lean_nat_to_int(v___x_1124_);
return v___x_1125_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__4(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__3, &l_Std_Time_PlainDate_weekOfYear___closed__3_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__3);
v___x_1127_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1128_ = lean_int_add(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__5(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1130_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__4, &l_Std_Time_PlainDate_weekOfYear___closed__4_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__4);
v___x_1131_ = lean_int_sub(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__6(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_range_1134_; 
v___x_1132_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1133_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__5, &l_Std_Time_PlainDate_weekOfYear___closed__5_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__5);
v_range_1134_ = lean_int_add(v___x_1133_, v___x_1132_);
return v_range_1134_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__7(void){
_start:
{
lean_object* v_range_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_range_1135_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1136_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_1137_ = lean_int_emod(v___x_1136_, v_range_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__8(void){
_start:
{
lean_object* v_range_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_range_1138_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1139_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__7, &l_Std_Time_PlainDate_weekOfYear___closed__7_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__7);
v___x_1140_ = lean_int_add(v___x_1139_, v_range_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__9(void){
_start:
{
lean_object* v_range_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_range_1141_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1142_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__8, &l_Std_Time_PlainDate_weekOfYear___closed__8_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__8);
v___x_1143_ = lean_int_emod(v___x_1142_, v_range_1141_);
return v___x_1143_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__10(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1145_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__9, &l_Std_Time_PlainDate_weekOfYear___closed__9_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__9);
v___x_1146_ = lean_int_add(v___x_1145_, v___x_1144_);
return v___x_1146_;
}
}
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object* v_date_1147_, uint8_t v_firstDay_1148_, lean_object* v_minDaysBounded_1149_){
_start:
{
lean_object* v_year_1150_; lean_object* v_thisYearStart_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_year_1150_ = lean_ctor_get(v_date_1147_, 0);
lean_inc_n(v_year_1150_, 2);
v_thisYearStart_1151_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1150_, v_firstDay_1148_, v_minDaysBounded_1149_);
v___x_1152_ = l_Std_Time_PlainDate_toEpochDay(v_date_1147_);
v___x_1153_ = l_Std_Time_PlainDate_toEpochDay(v_thisYearStart_1151_);
v___x_1154_ = lean_int_dec_lt(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_nextYearStart_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1155_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1156_ = lean_int_add(v_year_1150_, v___x_1155_);
lean_dec(v_year_1150_);
v_nextYearStart_1157_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1156_, v_firstDay_1148_, v_minDaysBounded_1149_);
v___x_1158_ = l_Std_Time_PlainDate_toEpochDay(v_nextYearStart_1157_);
v___x_1159_ = lean_int_dec_le(v___x_1158_, v___x_1152_);
lean_dec(v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v_interval_1160_; lean_object* v___x_1161_; lean_object* v_range_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_interval_1160_ = lean_int_sub(v___x_1152_, v___x_1153_);
lean_dec(v___x_1153_);
lean_dec(v___x_1152_);
v___x_1161_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v_range_1162_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__2, &l_Std_Time_PlainDate_weekOfYear___closed__2_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__2);
v___x_1163_ = lean_int_sub(v_interval_1160_, v___x_1161_);
lean_dec(v_interval_1160_);
v___x_1164_ = lean_int_emod(v___x_1163_, v_range_1162_);
lean_dec(v___x_1163_);
v___x_1165_ = lean_int_add(v___x_1164_, v_range_1162_);
lean_dec(v___x_1164_);
v___x_1166_ = lean_int_emod(v___x_1165_, v_range_1162_);
lean_dec(v___x_1165_);
v___x_1167_ = lean_int_add(v___x_1166_, v___x_1161_);
lean_dec(v___x_1166_);
v___x_1168_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1169_ = lean_int_ediv(v___x_1167_, v___x_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_int_add(v___x_1169_, v___x_1155_);
lean_dec(v___x_1169_);
return v___x_1170_;
}
else
{
lean_object* v___x_1171_; 
lean_dec(v___x_1153_);
lean_dec(v___x_1152_);
v___x_1171_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__10, &l_Std_Time_PlainDate_weekOfYear___closed__10_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__10);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_prevYearStart_1174_; lean_object* v___x_1175_; lean_object* v_interval_1176_; lean_object* v___x_1177_; lean_object* v_range_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec(v___x_1153_);
v___x_1172_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1173_ = lean_int_sub(v_year_1150_, v___x_1172_);
lean_dec(v_year_1150_);
v_prevYearStart_1174_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1173_, v_firstDay_1148_, v_minDaysBounded_1149_);
v___x_1175_ = l_Std_Time_PlainDate_toEpochDay(v_prevYearStart_1174_);
v_interval_1176_ = lean_int_sub(v___x_1152_, v___x_1175_);
lean_dec(v___x_1175_);
lean_dec(v___x_1152_);
v___x_1177_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v_range_1178_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__2, &l_Std_Time_PlainDate_weekOfYear___closed__2_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__2);
v___x_1179_ = lean_int_sub(v_interval_1176_, v___x_1177_);
lean_dec(v_interval_1176_);
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
v___x_1186_ = lean_int_add(v___x_1185_, v___x_1172_);
lean_dec(v___x_1185_);
return v___x_1186_;
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_weekOfYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1147_ = stack[0].m_obj;
uint8_t v_firstDay_1148_ = stack[1].m_num;
lean_object* v_minDaysBounded_1149_ = stack[2].m_obj;
lean_object* v_res_1187_;
v_res_1187_ = l_Std_Time_PlainDate_weekOfYear(v_date_1147_, v_firstDay_1148_, v_minDaysBounded_1149_);
stack->m_obj
 = v_res_1187_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear___boxed(lean_object* v_date_1188_, lean_object* v_firstDay_1189_, lean_object* v_minDaysBounded_1190_){
_start:
{
uint8_t v_firstDay_boxed_1191_; lean_object* v_res_1192_; 
v_firstDay_boxed_1191_ = lean_unbox(v_firstDay_1189_);
v_res_1192_ = l_Std_Time_PlainDate_weekOfYear(v_date_1188_, v_firstDay_boxed_1191_, v_minDaysBounded_1190_);
lean_dec(v_minDaysBounded_1190_);
return v_res_1192_;
}
}
lean_object* l_Std_Time_PlainDate_weekYear(lean_object* v_date_1193_, uint8_t v_firstDay_1194_, lean_object* v_minDays_1195_){
_start:
{
lean_object* v_year_1196_; lean_object* v_thisYearStart_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_year_1196_ = lean_ctor_get(v_date_1193_, 0);
lean_inc_n(v_year_1196_, 2);
v_thisYearStart_1197_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1196_, v_firstDay_1194_, v_minDays_1195_);
v___x_1198_ = l_Std_Time_PlainDate_toEpochDay(v_date_1193_);
v___x_1199_ = l_Std_Time_PlainDate_toEpochDay(v_thisYearStart_1197_);
v___x_1200_ = lean_int_dec_lt(v___x_1198_, v___x_1199_);
lean_dec(v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v_nextYearStart_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1201_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1202_ = lean_int_add(v_year_1196_, v___x_1201_);
lean_inc(v___x_1202_);
v_nextYearStart_1203_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1202_, v_firstDay_1194_, v_minDays_1195_);
v___x_1204_ = l_Std_Time_PlainDate_toEpochDay(v_nextYearStart_1203_);
v___x_1205_ = lean_int_dec_le(v___x_1204_, v___x_1198_);
lean_dec(v___x_1198_);
lean_dec(v___x_1204_);
if (v___x_1205_ == 0)
{
lean_dec(v___x_1202_);
return v_year_1196_;
}
else
{
lean_dec(v_year_1196_);
return v___x_1202_;
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec(v___x_1198_);
v___x_1206_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1207_ = lean_int_sub(v_year_1196_, v___x_1206_);
lean_dec(v_year_1196_);
return v___x_1207_;
}
}
}
LEAN_EXPORT void l_Std_Time_PlainDate_weekYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1193_ = stack[0].m_obj;
uint8_t v_firstDay_1194_ = stack[1].m_num;
lean_object* v_minDays_1195_ = stack[2].m_obj;
lean_object* v_res_1208_;
v_res_1208_ = l_Std_Time_PlainDate_weekYear(v_date_1193_, v_firstDay_1194_, v_minDays_1195_);
stack->m_obj
 = v_res_1208_;
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekYear___boxed(lean_object* v_date_1209_, lean_object* v_firstDay_1210_, lean_object* v_minDays_1211_){
_start:
{
uint8_t v_firstDay_boxed_1212_; lean_object* v_res_1213_; 
v_firstDay_boxed_1212_ = lean_unbox(v_firstDay_1210_);
v_res_1213_ = l_Std_Time_PlainDate_weekYear(v_date_1209_, v_firstDay_boxed_1212_, v_minDays_1211_);
lean_dec(v_minDays_1211_);
return v_res_1213_;
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
