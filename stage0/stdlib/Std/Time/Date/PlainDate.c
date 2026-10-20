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
uint8_t v___y_249_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_254_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_255_ = lean_int_mod(v_year_245_, v___x_254_);
v___x_256_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_257_ = lean_int_dec_eq(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
if (v___x_257_ == 0)
{
v___y_249_ = v___x_257_;
goto v___jp_248_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_258_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_259_ = lean_int_mod(v_year_245_, v___x_258_);
v___x_260_ = lean_int_dec_eq(v___x_259_, v___x_256_);
lean_dec(v___x_259_);
if (v___x_260_ == 0)
{
v___y_249_ = v___x_257_;
goto v___jp_248_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_262_ = lean_int_mod(v_year_245_, v___x_261_);
v___x_263_ = lean_int_dec_eq(v___x_262_, v___x_256_);
lean_dec(v___x_262_);
v___y_249_ = v___x_263_;
goto v___jp_248_;
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
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__17, &l_Std_Time_instInhabitedPlainDate___closed__17_once, _init_l_Std_Time_instInhabitedPlainDate___closed__17);
v___x_265_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__9, &l_Std_Time_instInhabitedPlainDate___closed__9_once, _init_l_Std_Time_instInhabitedPlainDate___closed__9);
v___x_266_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_264_);
return v___x_267_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited(void){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Std_Time_PlainDate_instInhabited___closed__0, &l_Std_Time_PlainDate_instInhabited___closed__0_once, _init_l_Std_Time_PlainDate_instInhabited___closed__0);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDay_x3f(lean_object* v_year_269_, lean_object* v_month_270_, lean_object* v_day_271_){
_start:
{
uint8_t v___y_273_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_279_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_280_ = lean_int_mod(v_year_269_, v___x_279_);
v___x_281_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_282_ = lean_int_dec_eq(v___x_280_, v___x_281_);
lean_dec(v___x_280_);
if (v___x_282_ == 0)
{
v___y_273_ = v___x_282_;
goto v___jp_272_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_284_ = lean_int_mod(v_year_269_, v___x_283_);
v___x_285_ = lean_int_dec_eq(v___x_284_, v___x_281_);
lean_dec(v___x_284_);
if (v___x_285_ == 0)
{
v___y_273_ = v___x_282_;
goto v___jp_272_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_287_ = lean_int_mod(v_year_269_, v___x_286_);
v___x_288_ = lean_int_dec_eq(v___x_287_, v___x_281_);
lean_dec(v___x_287_);
v___y_273_ = v___x_288_;
goto v___jp_272_;
}
}
v___jp_272_:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = l_Std_Time_Month_Ordinal_days(v___y_273_, v_month_270_);
v___x_275_ = lean_int_dec_le(v_day_271_, v___x_274_);
lean_dec(v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec(v_day_271_);
lean_dec(v_month_270_);
lean_dec(v_year_269_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_277_, 0, v_year_269_);
lean_ctor_set(v___x_277_, 1, v_month_270_);
lean_ctor_set(v___x_277_, 2, v_day_271_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal(lean_object* v_year_289_, lean_object* v_ordinal_290_){
_start:
{
uint8_t v___y_292_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_297_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_298_ = lean_int_mod(v_year_289_, v___x_297_);
v___x_299_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_300_ = lean_int_dec_eq(v___x_298_, v___x_299_);
lean_dec(v___x_298_);
if (v___x_300_ == 0)
{
v___y_292_ = v___x_300_;
goto v___jp_291_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_302_ = lean_int_mod(v_year_289_, v___x_301_);
v___x_303_ = lean_int_dec_eq(v___x_302_, v___x_299_);
lean_dec(v___x_302_);
if (v___x_303_ == 0)
{
v___y_292_ = v___x_300_;
goto v___jp_291_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_305_ = lean_int_mod(v_year_289_, v___x_304_);
v___x_306_ = lean_int_dec_eq(v___x_305_, v___x_299_);
lean_dec(v___x_305_);
v___y_292_ = v___x_306_;
goto v___jp_291_;
}
}
v___jp_291_:
{
lean_object* v_val_293_; lean_object* v_fst_294_; lean_object* v_snd_295_; lean_object* v___x_296_; 
v_val_293_ = l_Std_Time_ValidDate_ofOrdinal(v___y_292_, v_ordinal_290_);
v_fst_294_ = lean_ctor_get(v_val_293_, 0);
lean_inc(v_fst_294_);
v_snd_295_ = lean_ctor_get(v_val_293_, 1);
lean_inc(v_snd_295_);
lean_dec_ref(v_val_293_);
v___x_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_296_, 0, v_year_289_);
lean_ctor_set(v___x_296_, 1, v_fst_294_);
lean_ctor_set(v___x_296_, 2, v_snd_295_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal___boxed(lean_object* v_year_307_, lean_object* v_ordinal_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Time_PlainDate_ofYearOrdinal(v_year_307_, v_ordinal_308_);
lean_dec(v_ordinal_308_);
return v_res_309_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__0(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(719468u);
v___x_311_ = lean_nat_to_int(v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__1(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(31u);
v___x_313_ = lean_nat_to_int(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__2(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(12u);
v___x_315_ = lean_nat_to_int(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__3(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(146097u);
v___x_317_ = lean_nat_to_int(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__4(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1460u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__5(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(36524u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__6(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(146096u);
v___x_323_ = lean_nat_to_int(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__7(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(365u);
v___x_325_ = lean_nat_to_int(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__8(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(5u);
v___x_327_ = lean_nat_to_int(v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__9(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(2u);
v___x_329_ = lean_nat_to_int(v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__10(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_unsigned_to_nat(153u);
v___x_331_ = lean_nat_to_int(v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__11(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(10u);
v___x_333_ = lean_nat_to_int(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__12(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___x_335_ = lean_int_neg(v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofEpochDay___closed__13(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(3u);
v___x_337_ = lean_nat_to_int(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object* v_day_338_){
_start:
{
lean_object* v___y_340_; lean_object* v___y_341_; lean_object* v___y_342_; uint8_t v___y_343_; lean_object* v___x_348_; lean_object* v_z_349_; lean_object* v___x_350_; lean_object* v___y_352_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_365_; lean_object* v___y_366_; lean_object* v___y_367_; lean_object* v___y_368_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_389_; lean_object* v___y_390_; lean_object* v___y_391_; lean_object* v___y_392_; lean_object* v___y_393_; lean_object* v___y_394_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_401_; uint8_t v___x_444_; 
v___x_348_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__0, &l_Std_Time_PlainDate_ofEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__0);
v_z_349_ = lean_int_add(v_day_338_, v___x_348_);
v___x_350_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_444_ = lean_int_dec_le(v___x_350_, v_z_349_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__6, &l_Std_Time_PlainDate_ofEpochDay___closed__6_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__6);
v___x_446_ = lean_int_sub(v_z_349_, v___x_445_);
v___y_401_ = v___x_446_;
goto v___jp_400_;
}
else
{
lean_inc(v_z_349_);
v___y_401_ = v_z_349_;
goto v___jp_400_;
}
v___jp_339_:
{
lean_object* v_max_344_; uint8_t v___x_345_; 
v_max_344_ = l_Std_Time_Month_Ordinal_days(v___y_343_, v___y_341_);
v___x_345_ = lean_int_dec_lt(v_max_344_, v___y_340_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
lean_dec(v_max_344_);
v___x_346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_346_, 0, v___y_342_);
lean_ctor_set(v___x_346_, 1, v___y_341_);
lean_ctor_set(v___x_346_, 2, v___y_340_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; 
lean_dec(v___y_340_);
v___x_347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_347_, 0, v___y_342_);
lean_ctor_set(v___x_347_, 1, v___y_341_);
lean_ctor_set(v___x_347_, 2, v_max_344_);
return v___x_347_;
}
}
v___jp_351_:
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_int_mod(v___y_355_, v___y_352_);
v___x_359_ = lean_int_dec_eq(v___x_358_, v___x_350_);
lean_dec(v___x_358_);
if (v___x_359_ == 0)
{
v___y_340_ = v___y_357_;
v___y_341_ = v___y_353_;
v___y_342_ = v___y_355_;
v___y_343_ = v___x_359_;
goto v___jp_339_;
}
else
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_int_mod(v___y_355_, v___y_354_);
v___x_361_ = lean_int_dec_eq(v___x_360_, v___x_350_);
lean_dec(v___x_360_);
if (v___x_361_ == 0)
{
v___y_340_ = v___y_357_;
v___y_341_ = v___y_353_;
v___y_342_ = v___y_355_;
v___y_343_ = v___x_359_;
goto v___jp_339_;
}
else
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_int_mod(v___y_355_, v___y_356_);
v___x_363_ = lean_int_dec_eq(v___x_362_, v___x_350_);
lean_dec(v___x_362_);
v___y_340_ = v___y_357_;
v___y_341_ = v___y_353_;
v___y_342_ = v___y_355_;
v___y_343_ = v___x_363_;
goto v___jp_339_;
}
}
}
v___jp_364_:
{
uint8_t v___x_372_; 
v___x_372_ = lean_int_dec_le(v___y_367_, v___y_365_);
if (v___x_372_ == 0)
{
lean_dec(v___y_365_);
lean_inc(v___y_367_);
v___y_352_ = v___y_366_;
v___y_353_ = v___y_371_;
v___y_354_ = v___y_368_;
v___y_355_ = v___y_369_;
v___y_356_ = v___y_370_;
v___y_357_ = v___y_367_;
goto v___jp_351_;
}
else
{
lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_373_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__1, &l_Std_Time_PlainDate_ofEpochDay___closed__1_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__1);
v___x_374_ = lean_int_dec_le(v___y_365_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec(v___y_365_);
v___y_352_ = v___y_366_;
v___y_353_ = v___y_371_;
v___y_354_ = v___y_368_;
v___y_355_ = v___y_369_;
v___y_356_ = v___y_370_;
v___y_357_ = v___x_373_;
goto v___jp_351_;
}
else
{
v___y_352_ = v___y_366_;
v___y_353_ = v___y_371_;
v___y_354_ = v___y_368_;
v___y_355_ = v___y_369_;
v___y_356_ = v___y_370_;
v___y_357_ = v___y_365_;
goto v___jp_351_;
}
}
}
v___jp_375_:
{
lean_object* v_y_384_; uint8_t v___x_385_; 
v_y_384_ = lean_int_add(v___y_381_, v___y_383_);
lean_dec(v___y_381_);
v___x_385_ = lean_int_dec_le(v___y_378_, v___y_380_);
if (v___x_385_ == 0)
{
lean_dec(v___y_380_);
lean_inc(v___y_378_);
v___y_365_ = v___y_377_;
v___y_366_ = v___y_376_;
v___y_367_ = v___y_378_;
v___y_368_ = v___y_379_;
v___y_369_ = v_y_384_;
v___y_370_ = v___y_382_;
v___y_371_ = v___y_378_;
goto v___jp_364_;
}
else
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_387_ = lean_int_dec_le(v___y_380_, v___x_386_);
if (v___x_387_ == 0)
{
lean_dec(v___y_380_);
v___y_365_ = v___y_377_;
v___y_366_ = v___y_376_;
v___y_367_ = v___y_378_;
v___y_368_ = v___y_379_;
v___y_369_ = v_y_384_;
v___y_370_ = v___y_382_;
v___y_371_ = v___x_386_;
goto v___jp_364_;
}
else
{
v___y_365_ = v___y_377_;
v___y_366_ = v___y_376_;
v___y_367_ = v___y_378_;
v___y_368_ = v___y_379_;
v___y_369_ = v_y_384_;
v___y_370_ = v___y_382_;
v___y_371_ = v___y_380_;
goto v___jp_364_;
}
}
}
v___jp_388_:
{
lean_object* v_m_398_; uint8_t v___x_399_; 
v_m_398_ = lean_int_add(v___y_394_, v___y_397_);
lean_dec(v___y_394_);
v___x_399_ = lean_int_dec_le(v_m_398_, v___y_395_);
if (v___x_399_ == 0)
{
v___y_376_ = v___y_390_;
v___y_377_ = v___y_389_;
v___y_378_ = v___y_391_;
v___y_379_ = v___y_392_;
v___y_380_ = v_m_398_;
v___y_381_ = v___y_393_;
v___y_382_ = v___y_396_;
v___y_383_ = v___x_350_;
goto v___jp_375_;
}
else
{
v___y_376_ = v___y_390_;
v___y_377_ = v___y_389_;
v___y_378_ = v___y_391_;
v___y_379_ = v___y_392_;
v___y_380_ = v_m_398_;
v___y_381_ = v___y_393_;
v___y_382_ = v___y_396_;
v___y_383_ = v___y_391_;
goto v___jp_375_;
}
}
v___jp_400_:
{
lean_object* v___x_402_; lean_object* v_era_403_; lean_object* v___x_404_; lean_object* v_doe_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_yoe_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_y_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_doy_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_mp_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_d_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_402_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__3, &l_Std_Time_PlainDate_ofEpochDay___closed__3_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__3);
v_era_403_ = lean_int_div(v___y_401_, v___x_402_);
lean_dec(v___y_401_);
v___x_404_ = lean_int_mul(v_era_403_, v___x_402_);
v_doe_405_ = lean_int_sub(v_z_349_, v___x_404_);
lean_dec(v___x_404_);
lean_dec(v_z_349_);
v___x_406_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__4, &l_Std_Time_PlainDate_ofEpochDay___closed__4_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__4);
v___x_407_ = lean_int_div(v_doe_405_, v___x_406_);
v___x_408_ = lean_int_sub(v_doe_405_, v___x_407_);
lean_dec(v___x_407_);
v___x_409_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__5, &l_Std_Time_PlainDate_ofEpochDay___closed__5_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__5);
v___x_410_ = lean_int_div(v_doe_405_, v___x_409_);
v___x_411_ = lean_int_add(v___x_408_, v___x_410_);
lean_dec(v___x_410_);
lean_dec(v___x_408_);
v___x_412_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__6, &l_Std_Time_PlainDate_ofEpochDay___closed__6_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__6);
v___x_413_ = lean_int_div(v_doe_405_, v___x_412_);
v___x_414_ = lean_int_sub(v___x_411_, v___x_413_);
lean_dec(v___x_413_);
lean_dec(v___x_411_);
v___x_415_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__7, &l_Std_Time_PlainDate_ofEpochDay___closed__7_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__7);
v_yoe_416_ = lean_int_div(v___x_414_, v___x_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_418_ = lean_int_mul(v_era_403_, v___x_417_);
lean_dec(v_era_403_);
v_y_419_ = lean_int_add(v_yoe_416_, v___x_418_);
lean_dec(v___x_418_);
v___x_420_ = lean_int_mul(v___x_415_, v_yoe_416_);
v___x_421_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_422_ = lean_int_div(v_yoe_416_, v___x_421_);
v___x_423_ = lean_int_add(v___x_420_, v___x_422_);
lean_dec(v___x_422_);
lean_dec(v___x_420_);
v___x_424_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_425_ = lean_int_div(v_yoe_416_, v___x_424_);
lean_dec(v_yoe_416_);
v___x_426_ = lean_int_sub(v___x_423_, v___x_425_);
lean_dec(v___x_425_);
lean_dec(v___x_423_);
v_doy_427_ = lean_int_sub(v_doe_405_, v___x_426_);
lean_dec(v___x_426_);
lean_dec(v_doe_405_);
v___x_428_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_429_ = lean_int_mul(v___x_428_, v_doy_427_);
v___x_430_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__9, &l_Std_Time_PlainDate_ofEpochDay___closed__9_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__9);
v___x_431_ = lean_int_add(v___x_429_, v___x_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__10, &l_Std_Time_PlainDate_ofEpochDay___closed__10_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__10);
v_mp_433_ = lean_int_div(v___x_431_, v___x_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_int_mul(v___x_432_, v_mp_433_);
v___x_435_ = lean_int_add(v___x_434_, v___x_430_);
lean_dec(v___x_434_);
v___x_436_ = lean_int_div(v___x_435_, v___x_428_);
lean_dec(v___x_435_);
v___x_437_ = lean_int_sub(v_doy_427_, v___x_436_);
lean_dec(v___x_436_);
lean_dec(v_doy_427_);
v___x_438_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_d_439_ = lean_int_add(v___x_437_, v___x_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__11, &l_Std_Time_PlainDate_ofEpochDay___closed__11_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__11);
v___x_441_ = lean_int_dec_lt(v_mp_433_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__12, &l_Std_Time_PlainDate_ofEpochDay___closed__12_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__12);
v___y_389_ = v_d_439_;
v___y_390_ = v___x_421_;
v___y_391_ = v___x_438_;
v___y_392_ = v___x_424_;
v___y_393_ = v_y_419_;
v___y_394_ = v_mp_433_;
v___y_395_ = v___x_430_;
v___y_396_ = v___x_417_;
v___y_397_ = v___x_442_;
goto v___jp_388_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___y_389_ = v_d_439_;
v___y_390_ = v___x_421_;
v___y_391_ = v___x_438_;
v___y_392_ = v___x_424_;
v___y_393_ = v_y_419_;
v___y_394_ = v_mp_433_;
v___y_395_ = v___x_430_;
v___y_396_ = v___x_417_;
v___y_397_ = v___x_443_;
goto v___jp_388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofEpochDay___boxed(lean_object* v_day_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_Time_PlainDate_ofEpochDay(v_day_447_);
lean_dec(v_day_447_);
return v_res_448_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_450_ = lean_int_neg(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object* v_date_451_){
_start:
{
lean_object* v_day_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_day_452_ = lean_ctor_get(v_date_451_, 2);
v___x_453_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_454_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_455_ = lean_obj_once(&l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0, &l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0);
v___x_456_ = lean_int_add(v_day_452_, v___x_455_);
v___x_457_ = lean_int_ediv(v___x_456_, v___x_454_);
lean_dec(v___x_456_);
v___x_458_ = lean_int_add(v___x_457_, v___x_453_);
lean_dec(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth___boxed(lean_object* v_date_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_459_);
lean_dec_ref(v_date_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object* v_date_461_){
_start:
{
lean_object* v_month_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_month_462_ = lean_ctor_get(v_date_461_, 1);
v___x_463_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_464_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___x_465_ = lean_obj_once(&l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0, &l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0);
v___x_466_ = lean_int_add(v_month_462_, v___x_465_);
v___x_467_ = lean_int_ediv(v___x_466_, v___x_464_);
lean_dec(v___x_466_);
v___x_468_ = lean_int_add(v___x_467_, v___x_463_);
lean_dec(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object* v_date_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_Time_PlainDate_quarter(v_date_469_);
lean_dec_ref(v_date_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object* v_date_471_){
_start:
{
lean_object* v_year_472_; lean_object* v_month_473_; lean_object* v_day_474_; uint8_t v___y_476_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_year_472_ = lean_ctor_get(v_date_471_, 0);
v_month_473_ = lean_ctor_get(v_date_471_, 1);
v_day_474_ = lean_ctor_get(v_date_471_, 2);
v___x_479_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_480_ = lean_int_mod(v_year_472_, v___x_479_);
v___x_481_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_482_ = lean_int_dec_eq(v___x_480_, v___x_481_);
lean_dec(v___x_480_);
if (v___x_482_ == 0)
{
v___y_476_ = v___x_482_;
goto v___jp_475_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_483_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_484_ = lean_int_mod(v_year_472_, v___x_483_);
v___x_485_ = lean_int_dec_eq(v___x_484_, v___x_481_);
lean_dec(v___x_484_);
if (v___x_485_ == 0)
{
v___y_476_ = v___x_482_;
goto v___jp_475_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_487_ = lean_int_mod(v_year_472_, v___x_486_);
v___x_488_ = lean_int_dec_eq(v___x_487_, v___x_481_);
lean_dec(v___x_487_);
v___y_476_ = v___x_488_;
goto v___jp_475_;
}
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_inc(v_day_474_);
lean_inc(v_month_473_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_month_473_);
lean_ctor_set(v___x_477_, 1, v_day_474_);
v___x_478_ = l_Std_Time_ValidDate_dayOfYear(v___y_476_, v___x_477_);
lean_dec_ref_known(v___x_477_, 2);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object* v_date_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_Time_PlainDate_dayOfYear(v_date_489_);
lean_dec_ref(v_date_489_);
return v_res_490_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_era(lean_object* v_date_491_){
_start:
{
lean_object* v_year_492_; uint8_t v___x_493_; 
v_year_492_ = lean_ctor_get(v_date_491_, 0);
v___x_493_ = l_Std_Time_Year_Offset_era(v_year_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object* v_date_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Std_Time_PlainDate_era(v_date_494_);
lean_dec_ref(v_date_494_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object* v_date_497_){
_start:
{
lean_object* v_year_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_year_498_ = lean_ctor_get(v_date_497_, 0);
v___x_499_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_500_ = lean_int_mod(v_year_498_, v___x_499_);
v___x_501_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_502_ = lean_int_dec_eq(v___x_500_, v___x_501_);
lean_dec(v___x_500_);
if (v___x_502_ == 0)
{
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_504_ = lean_int_mod(v_year_498_, v___x_503_);
v___x_505_ = lean_int_dec_eq(v___x_504_, v___x_501_);
lean_dec(v___x_504_);
if (v___x_505_ == 0)
{
return v___x_502_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_507_ = lean_int_mod(v_year_498_, v___x_506_);
v___x_508_ = lean_int_dec_eq(v___x_507_, v___x_501_);
lean_dec(v___x_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object* v_date_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_Std_Time_PlainDate_inLeapYear(v_date_509_);
lean_dec_ref(v_date_509_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toEpochDay___closed__0(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__13, &l_Std_Time_PlainDate_ofEpochDay___closed__13_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__13);
v___x_513_ = lean_int_neg(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toEpochDay___closed__1(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(399u);
v___x_515_ = lean_nat_to_int(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object* v_date_516_){
_start:
{
lean_object* v_year_517_; lean_object* v_month_518_; lean_object* v_day_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_560_; uint8_t v___x_565_; 
v_year_517_ = lean_ctor_get(v_date_516_, 0);
lean_inc(v_year_517_);
v_month_518_ = lean_ctor_get(v_date_516_, 1);
lean_inc(v_month_518_);
v_day_519_ = lean_ctor_get(v_date_516_, 2);
lean_inc(v_day_519_);
lean_dec_ref(v_date_516_);
v___x_520_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__9, &l_Std_Time_PlainDate_ofEpochDay___closed__9_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__9);
v___x_521_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_565_ = lean_int_dec_lt(v___x_520_, v_month_518_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
v___x_566_ = lean_int_sub(v_year_517_, v___x_521_);
lean_dec(v_year_517_);
v___y_560_ = v___x_566_;
goto v___jp_559_;
}
else
{
v___y_560_ = v_year_517_;
goto v___jp_559_;
}
v___jp_522_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_doy_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v_doe_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_527_ = lean_int_add(v_month_518_, v___y_526_);
lean_dec(v_month_518_);
v___x_528_ = lean_int_mul(v___y_525_, v___x_527_);
lean_dec(v___x_527_);
v___x_529_ = lean_int_add(v___x_528_, v___x_520_);
lean_dec(v___x_528_);
v___x_530_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_531_ = lean_int_div(v___x_529_, v___x_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_int_add(v___x_531_, v_day_519_);
lean_dec(v_day_519_);
lean_dec(v___x_531_);
v_doy_533_ = lean_int_sub(v___x_532_, v___x_521_);
lean_dec(v___x_532_);
v___x_534_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__7, &l_Std_Time_PlainDate_ofEpochDay___closed__7_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__7);
v___x_535_ = lean_int_mul(v___y_524_, v___x_534_);
v___x_536_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_537_ = lean_int_div(v___y_524_, v___x_536_);
v___x_538_ = lean_int_add(v___x_535_, v___x_537_);
lean_dec(v___x_537_);
lean_dec(v___x_535_);
v___x_539_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_540_ = lean_int_div(v___y_524_, v___x_539_);
lean_dec(v___y_524_);
v___x_541_ = lean_int_sub(v___x_538_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v___x_538_);
v_doe_542_ = lean_int_add(v___x_541_, v_doy_533_);
lean_dec(v_doy_533_);
lean_dec(v___x_541_);
v___x_543_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__3, &l_Std_Time_PlainDate_ofEpochDay___closed__3_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__3);
v___x_544_ = lean_int_mul(v___y_523_, v___x_543_);
lean_dec(v___y_523_);
v___x_545_ = lean_int_add(v___x_544_, v_doe_542_);
lean_dec(v_doe_542_);
lean_dec(v___x_544_);
v___x_546_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__0, &l_Std_Time_PlainDate_ofEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__0);
v___x_547_ = lean_int_sub(v___x_545_, v___x_546_);
lean_dec(v___x_545_);
return v___x_547_;
}
v___jp_548_:
{
lean_object* v___x_551_; lean_object* v_era_552_; lean_object* v___x_553_; lean_object* v_yoe_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_551_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v_era_552_ = lean_int_div(v___y_550_, v___x_551_);
lean_dec(v___y_550_);
v___x_553_ = lean_int_mul(v_era_552_, v___x_551_);
v_yoe_554_ = lean_int_sub(v___y_549_, v___x_553_);
lean_dec(v___x_553_);
lean_dec(v___y_549_);
v___x_555_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__10, &l_Std_Time_PlainDate_ofEpochDay___closed__10_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__10);
v___x_556_ = lean_int_dec_lt(v___x_520_, v_month_518_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
v___x_557_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___y_523_ = v_era_552_;
v___y_524_ = v_yoe_554_;
v___y_525_ = v___x_555_;
v___y_526_ = v___x_557_;
goto v___jp_522_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = lean_obj_once(&l_Std_Time_PlainDate_toEpochDay___closed__0, &l_Std_Time_PlainDate_toEpochDay___closed__0_once, _init_l_Std_Time_PlainDate_toEpochDay___closed__0);
v___y_523_ = v_era_552_;
v___y_524_ = v_yoe_554_;
v___y_525_ = v___x_555_;
v___y_526_ = v___x_558_;
goto v___jp_522_;
}
}
v___jp_559_:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_562_ = lean_int_dec_le(v___x_561_, v___y_560_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_obj_once(&l_Std_Time_PlainDate_toEpochDay___closed__1, &l_Std_Time_PlainDate_toEpochDay___closed__1_once, _init_l_Std_Time_PlainDate_toEpochDay___closed__1);
v___x_564_ = lean_int_sub(v___y_560_, v___x_563_);
v___y_549_ = v___y_560_;
v___y_550_ = v___x_564_;
goto v___jp_548_;
}
else
{
lean_inc(v___y_560_);
v___y_549_ = v___y_560_;
v___y_550_ = v___y_560_;
goto v___jp_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays(lean_object* v_date_567_, lean_object* v_days_568_){
_start:
{
lean_object* v_dateDays_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_dateDays_569_ = l_Std_Time_PlainDate_toEpochDay(v_date_567_);
v___x_570_ = lean_int_add(v_dateDays_569_, v_days_568_);
lean_dec(v_dateDays_569_);
v___x_571_ = l_Std_Time_PlainDate_ofEpochDay(v___x_570_);
lean_dec(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays___boxed(lean_object* v_date_572_, lean_object* v_days_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Time_PlainDate_addDays(v_date_572_, v_days_573_);
lean_dec(v_days_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays(lean_object* v_date_575_, lean_object* v_days_576_){
_start:
{
lean_object* v___x_577_; lean_object* v_dateDays_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_int_neg(v_days_576_);
v_dateDays_578_ = l_Std_Time_PlainDate_toEpochDay(v_date_575_);
v___x_579_ = lean_int_add(v_dateDays_578_, v___x_577_);
lean_dec(v___x_577_);
lean_dec(v_dateDays_578_);
v___x_580_ = l_Std_Time_PlainDate_ofEpochDay(v___x_579_);
lean_dec(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays___boxed(lean_object* v_date_581_, lean_object* v_days_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Time_PlainDate_subDays(v_date_581_, v_days_582_);
lean_dec(v_days_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks(lean_object* v_date_584_, lean_object* v_weeks_585_){
_start:
{
lean_object* v_dateDays_586_; lean_object* v___x_587_; lean_object* v_daysToAdd_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_dateDays_586_ = l_Std_Time_PlainDate_toEpochDay(v_date_584_);
v___x_587_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_588_ = lean_int_mul(v_weeks_585_, v___x_587_);
v___x_589_ = lean_int_add(v_dateDays_586_, v_daysToAdd_588_);
lean_dec(v_daysToAdd_588_);
lean_dec(v_dateDays_586_);
v___x_590_ = l_Std_Time_PlainDate_ofEpochDay(v___x_589_);
lean_dec(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks___boxed(lean_object* v_date_591_, lean_object* v_weeks_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_Time_PlainDate_addWeeks(v_date_591_, v_weeks_592_);
lean_dec(v_weeks_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks(lean_object* v_date_594_, lean_object* v_weeks_595_){
_start:
{
lean_object* v___x_596_; lean_object* v_dateDays_597_; lean_object* v___x_598_; lean_object* v_daysToAdd_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_596_ = lean_int_neg(v_weeks_595_);
v_dateDays_597_ = l_Std_Time_PlainDate_toEpochDay(v_date_594_);
v___x_598_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_599_ = lean_int_mul(v___x_596_, v___x_598_);
lean_dec(v___x_596_);
v___x_600_ = lean_int_add(v_dateDays_597_, v_daysToAdd_599_);
lean_dec(v_daysToAdd_599_);
lean_dec(v_dateDays_597_);
v___x_601_ = l_Std_Time_PlainDate_ofEpochDay(v___x_600_);
lean_dec(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks___boxed(lean_object* v_date_602_, lean_object* v_weeks_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_Time_PlainDate_subWeeks(v_date_602_, v_weeks_603_);
lean_dec(v_weeks_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object* v_date_605_, lean_object* v_months_606_){
_start:
{
lean_object* v_year_607_; lean_object* v_month_608_; lean_object* v_day_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_641_; 
v_year_607_ = lean_ctor_get(v_date_605_, 0);
v_month_608_ = lean_ctor_get(v_date_605_, 1);
v_day_609_ = lean_ctor_get(v_date_605_, 2);
v_isSharedCheck_641_ = !lean_is_exclusive(v_date_605_);
if (v_isSharedCheck_641_ == 0)
{
v___x_611_ = v_date_605_;
v_isShared_612_ = v_isSharedCheck_641_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_day_609_);
lean_inc(v_month_608_);
lean_inc(v_year_607_);
lean_dec(v_date_605_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_641_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_totalMonths_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_wrappedMonths_618_; lean_object* v_yearsOffset_619_; lean_object* v___x_620_; uint8_t v___y_622_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_613_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_614_ = lean_int_sub(v_month_608_, v___x_613_);
lean_dec(v_month_608_);
v_totalMonths_615_ = lean_int_add(v___x_614_, v_months_606_);
lean_dec(v___x_614_);
v___x_616_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_617_ = lean_int_emod(v_totalMonths_615_, v___x_616_);
v_wrappedMonths_618_ = lean_int_add(v___x_617_, v___x_613_);
lean_dec(v___x_617_);
v_yearsOffset_619_ = lean_int_ediv(v_totalMonths_615_, v___x_616_);
lean_dec(v_totalMonths_615_);
v___x_620_ = lean_int_add(v_year_607_, v_yearsOffset_619_);
lean_dec(v_yearsOffset_619_);
lean_dec(v_year_607_);
v___x_631_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_632_ = lean_int_mod(v___x_620_, v___x_631_);
v___x_633_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_634_ = lean_int_dec_eq(v___x_632_, v___x_633_);
lean_dec(v___x_632_);
if (v___x_634_ == 0)
{
v___y_622_ = v___x_634_;
goto v___jp_621_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_636_ = lean_int_mod(v___x_620_, v___x_635_);
v___x_637_ = lean_int_dec_eq(v___x_636_, v___x_633_);
lean_dec(v___x_636_);
if (v___x_637_ == 0)
{
v___y_622_ = v___x_634_;
goto v___jp_621_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_639_ = lean_int_mod(v___x_620_, v___x_638_);
v___x_640_ = lean_int_dec_eq(v___x_639_, v___x_633_);
lean_dec(v___x_639_);
v___y_622_ = v___x_640_;
goto v___jp_621_;
}
}
v___jp_621_:
{
lean_object* v_max_623_; uint8_t v___x_624_; 
v_max_623_ = l_Std_Time_Month_Ordinal_days(v___y_622_, v_wrappedMonths_618_);
v___x_624_ = lean_int_dec_lt(v_max_623_, v_day_609_);
if (v___x_624_ == 0)
{
lean_object* v___x_626_; 
lean_dec(v_max_623_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v_wrappedMonths_618_);
lean_ctor_set(v___x_611_, 0, v___x_620_);
v___x_626_ = v___x_611_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_wrappedMonths_618_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_day_609_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v___x_629_; 
lean_dec(v_day_609_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 2, v_max_623_);
lean_ctor_set(v___x_611_, 1, v_wrappedMonths_618_);
lean_ctor_set(v___x_611_, 0, v___x_620_);
v___x_629_ = v___x_611_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_wrappedMonths_618_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_max_623_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip___boxed(lean_object* v_date_642_, lean_object* v_months_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_Time_PlainDate_addMonthsClip(v_date_642_, v_months_643_);
lean_dec(v_months_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip(lean_object* v_date_645_, lean_object* v_months_646_){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_int_neg(v_months_646_);
v___x_648_ = l_Std_Time_PlainDate_addMonthsClip(v_date_645_, v___x_647_);
lean_dec(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip___boxed(lean_object* v_date_649_, lean_object* v_months_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Time_PlainDate_subMonthsClip(v_date_649_, v_months_650_);
lean_dec(v_months_650_);
return v_res_651_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__0(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_unsigned_to_nat(30u);
v___x_653_ = lean_nat_to_int(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__1(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_654_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__0, &l_Std_Time_PlainDate_rollOver___closed__0_once, _init_l_Std_Time_PlainDate_rollOver___closed__0);
v___x_655_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_656_ = lean_int_add(v___x_655_, v___x_654_);
return v___x_656_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__2(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_658_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__1, &l_Std_Time_PlainDate_rollOver___closed__1_once, _init_l_Std_Time_PlainDate_rollOver___closed__1);
v___x_659_ = lean_int_sub(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__3(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_range_662_; 
v___x_660_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_661_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__2, &l_Std_Time_PlainDate_rollOver___closed__2_once, _init_l_Std_Time_PlainDate_rollOver___closed__2);
v_range_662_ = lean_int_add(v___x_661_, v___x_660_);
return v_range_662_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__4(void){
_start:
{
lean_object* v_range_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_range_663_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_664_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_665_ = lean_int_emod(v___x_664_, v_range_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__5(void){
_start:
{
lean_object* v_range_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_range_666_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_667_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__4, &l_Std_Time_PlainDate_rollOver___closed__4_once, _init_l_Std_Time_PlainDate_rollOver___closed__4);
v___x_668_ = lean_int_add(v___x_667_, v_range_666_);
return v___x_668_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__6(void){
_start:
{
lean_object* v_range_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_range_669_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_670_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__5, &l_Std_Time_PlainDate_rollOver___closed__5_once, _init_l_Std_Time_PlainDate_rollOver___closed__5);
v___x_671_ = lean_int_emod(v___x_670_, v_range_669_);
return v___x_671_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__7(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_673_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__6, &l_Std_Time_PlainDate_rollOver___closed__6_once, _init_l_Std_Time_PlainDate_rollOver___closed__6);
v___x_674_ = lean_int_add(v___x_673_, v___x_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver(lean_object* v_year_675_, lean_object* v_month_676_, lean_object* v_day_677_){
_start:
{
lean_object* v___y_679_; lean_object* v___x_685_; uint8_t v___y_687_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_685_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_692_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_693_ = lean_int_mod(v_year_675_, v___x_692_);
v___x_694_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_695_ = lean_int_dec_eq(v___x_693_, v___x_694_);
lean_dec(v___x_693_);
if (v___x_695_ == 0)
{
v___y_687_ = v___x_695_;
goto v___jp_686_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_696_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_697_ = lean_int_mod(v_year_675_, v___x_696_);
v___x_698_ = lean_int_dec_eq(v___x_697_, v___x_694_);
lean_dec(v___x_697_);
if (v___x_698_ == 0)
{
v___y_687_ = v___x_695_;
goto v___jp_686_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_699_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_700_ = lean_int_mod(v_year_675_, v___x_699_);
v___x_701_ = lean_int_dec_eq(v___x_700_, v___x_694_);
lean_dec(v___x_700_);
v___y_687_ = v___x_701_;
goto v___jp_686_;
}
}
v___jp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v_dateDays_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_680_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_681_ = lean_int_sub(v_day_677_, v___x_680_);
v_dateDays_682_ = l_Std_Time_PlainDate_toEpochDay(v___y_679_);
v___x_683_ = lean_int_add(v_dateDays_682_, v___x_681_);
lean_dec(v___x_681_);
lean_dec(v_dateDays_682_);
v___x_684_ = l_Std_Time_PlainDate_ofEpochDay(v___x_683_);
lean_dec(v___x_683_);
return v___x_684_;
}
v___jp_686_:
{
lean_object* v_max_688_; uint8_t v___x_689_; 
v_max_688_ = l_Std_Time_Month_Ordinal_days(v___y_687_, v_month_676_);
v___x_689_ = lean_int_dec_lt(v_max_688_, v___x_685_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
lean_dec(v_max_688_);
v___x_690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_690_, 0, v_year_675_);
lean_ctor_set(v___x_690_, 1, v_month_676_);
lean_ctor_set(v___x_690_, 2, v___x_685_);
v___y_679_ = v___x_690_;
goto v___jp_678_;
}
else
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_691_, 0, v_year_675_);
lean_ctor_set(v___x_691_, 1, v_month_676_);
lean_ctor_set(v___x_691_, 2, v_max_688_);
v___y_679_ = v___x_691_;
goto v___jp_678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver___boxed(lean_object* v_year_702_, lean_object* v_month_703_, lean_object* v_day_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Std_Time_PlainDate_rollOver(v_year_702_, v_month_703_, v_day_704_);
lean_dec(v_day_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip(lean_object* v_dt_706_, lean_object* v_year_707_){
_start:
{
lean_object* v_month_708_; lean_object* v_day_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_733_; 
v_month_708_ = lean_ctor_get(v_dt_706_, 1);
v_day_709_ = lean_ctor_get(v_dt_706_, 2);
v_isSharedCheck_733_ = !lean_is_exclusive(v_dt_706_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_dt_706_, 0);
lean_dec(v_unused_734_);
v___x_711_ = v_dt_706_;
v_isShared_712_ = v_isSharedCheck_733_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_day_709_);
lean_inc(v_month_708_);
lean_dec(v_dt_706_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_733_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
uint8_t v___y_714_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_723_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_724_ = lean_int_mod(v_year_707_, v___x_723_);
v___x_725_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_726_ = lean_int_dec_eq(v___x_724_, v___x_725_);
lean_dec(v___x_724_);
if (v___x_726_ == 0)
{
v___y_714_ = v___x_726_;
goto v___jp_713_;
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_727_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_728_ = lean_int_mod(v_year_707_, v___x_727_);
v___x_729_ = lean_int_dec_eq(v___x_728_, v___x_725_);
lean_dec(v___x_728_);
if (v___x_729_ == 0)
{
v___y_714_ = v___x_726_;
goto v___jp_713_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_730_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_731_ = lean_int_mod(v_year_707_, v___x_730_);
v___x_732_ = lean_int_dec_eq(v___x_731_, v___x_725_);
lean_dec(v___x_731_);
v___y_714_ = v___x_732_;
goto v___jp_713_;
}
}
v___jp_713_:
{
lean_object* v_max_715_; uint8_t v___x_716_; 
v_max_715_ = l_Std_Time_Month_Ordinal_days(v___y_714_, v_month_708_);
v___x_716_ = lean_int_dec_lt(v_max_715_, v_day_709_);
if (v___x_716_ == 0)
{
lean_object* v___x_718_; 
lean_dec(v_max_715_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v_year_707_);
v___x_718_ = v___x_711_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_year_707_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_month_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_day_709_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
else
{
lean_object* v___x_721_; 
lean_dec(v_day_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 2, v_max_715_);
lean_ctor_set(v___x_711_, 0, v_year_707_);
v___x_721_ = v___x_711_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_year_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_month_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_max_715_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearRollOver(lean_object* v_dt_735_, lean_object* v_year_736_){
_start:
{
lean_object* v_month_737_; lean_object* v_day_738_; lean_object* v___x_739_; 
v_month_737_ = lean_ctor_get(v_dt_735_, 1);
lean_inc(v_month_737_);
v_day_738_ = lean_ctor_get(v_dt_735_, 2);
lean_inc(v_day_738_);
lean_dec_ref(v_dt_735_);
v___x_739_ = l_Std_Time_PlainDate_rollOver(v_year_736_, v_month_737_, v_day_738_);
lean_dec(v_day_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object* v_date_740_, lean_object* v_months_741_){
_start:
{
lean_object* v_year_742_; lean_object* v_month_743_; lean_object* v_day_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_777_; 
v_year_742_ = lean_ctor_get(v_date_740_, 0);
v_month_743_ = lean_ctor_get(v_date_740_, 1);
v_day_744_ = lean_ctor_get(v_date_740_, 2);
v_isSharedCheck_777_ = !lean_is_exclusive(v_date_740_);
if (v_isSharedCheck_777_ == 0)
{
v___x_746_ = v_date_740_;
v_isShared_747_ = v_isSharedCheck_777_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_day_744_);
lean_inc(v_month_743_);
lean_inc(v_year_742_);
lean_dec(v_date_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_777_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___y_749_; lean_object* v___x_756_; uint8_t v___y_758_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_756_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_767_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_768_ = lean_int_mod(v_year_742_, v___x_767_);
v___x_769_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_770_ = lean_int_dec_eq(v___x_768_, v___x_769_);
lean_dec(v___x_768_);
if (v___x_770_ == 0)
{
v___y_758_ = v___x_770_;
goto v___jp_757_;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_772_ = lean_int_mod(v_year_742_, v___x_771_);
v___x_773_ = lean_int_dec_eq(v___x_772_, v___x_769_);
lean_dec(v___x_772_);
if (v___x_773_ == 0)
{
v___y_758_ = v___x_770_;
goto v___jp_757_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_775_ = lean_int_mod(v_year_742_, v___x_774_);
v___x_776_ = lean_int_dec_eq(v___x_775_, v___x_769_);
lean_dec(v___x_775_);
v___y_758_ = v___x_776_;
goto v___jp_757_;
}
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v_dateDays_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_750_ = l_Std_Time_PlainDate_addMonthsClip(v___y_749_, v_months_741_);
v___x_751_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_752_ = lean_int_sub(v_day_744_, v___x_751_);
lean_dec(v_day_744_);
v_dateDays_753_ = l_Std_Time_PlainDate_toEpochDay(v___x_750_);
v___x_754_ = lean_int_add(v_dateDays_753_, v___x_752_);
lean_dec(v___x_752_);
lean_dec(v_dateDays_753_);
v___x_755_ = l_Std_Time_PlainDate_ofEpochDay(v___x_754_);
lean_dec(v___x_754_);
return v___x_755_;
}
v___jp_757_:
{
lean_object* v_max_759_; uint8_t v___x_760_; 
v_max_759_ = l_Std_Time_Month_Ordinal_days(v___y_758_, v_month_743_);
v___x_760_ = lean_int_dec_lt(v_max_759_, v___x_756_);
if (v___x_760_ == 0)
{
lean_object* v___x_762_; 
lean_dec(v_max_759_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 2, v___x_756_);
v___x_762_ = v___x_746_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_year_742_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_month_743_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v___x_756_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
v___y_749_ = v___x_762_;
goto v___jp_748_;
}
}
else
{
lean_object* v___x_765_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 2, v_max_759_);
v___x_765_ = v___x_746_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_year_742_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_month_743_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v_max_759_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
v___y_749_ = v___x_765_;
goto v___jp_748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver___boxed(lean_object* v_date_778_, lean_object* v_months_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_778_, v_months_779_);
lean_dec(v_months_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver(lean_object* v_date_781_, lean_object* v_months_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_int_neg(v_months_782_);
v___x_784_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_781_, v___x_783_);
lean_dec(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver___boxed(lean_object* v_date_785_, lean_object* v_months_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_Time_PlainDate_subMonthsRollOver(v_date_785_, v_months_786_);
lean_dec(v_months_786_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver(lean_object* v_date_788_, lean_object* v_years_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_791_ = lean_int_mul(v_years_789_, v___x_790_);
v___x_792_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_788_, v___x_791_);
lean_dec(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver___boxed(lean_object* v_date_793_, lean_object* v_years_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_Time_PlainDate_addYearsRollOver(v_date_793_, v_years_794_);
lean_dec(v_years_794_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver(lean_object* v_date_796_, lean_object* v_years_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_799_ = lean_int_mul(v_years_797_, v___x_798_);
v___x_800_ = lean_int_neg(v___x_799_);
lean_dec(v___x_799_);
v___x_801_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_796_, v___x_800_);
lean_dec(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver___boxed(lean_object* v_date_802_, lean_object* v_years_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_Time_PlainDate_subYearsRollOver(v_date_802_, v_years_803_);
lean_dec(v_years_803_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip(lean_object* v_date_805_, lean_object* v_years_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_808_ = lean_int_mul(v_years_806_, v___x_807_);
v___x_809_ = l_Std_Time_PlainDate_addMonthsClip(v_date_805_, v___x_808_);
lean_dec(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip___boxed(lean_object* v_date_810_, lean_object* v_years_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_Time_PlainDate_addYearsClip(v_date_810_, v_years_811_);
lean_dec(v_years_811_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip(lean_object* v_date_813_, lean_object* v_years_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_815_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__2, &l_Std_Time_PlainDate_ofEpochDay___closed__2_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__2);
v___x_816_ = lean_int_mul(v_years_814_, v___x_815_);
v___x_817_ = lean_int_neg(v___x_816_);
lean_dec(v___x_816_);
v___x_818_ = l_Std_Time_PlainDate_addMonthsClip(v_date_813_, v___x_817_);
lean_dec(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip___boxed(lean_object* v_date_819_, lean_object* v_years_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Std_Time_PlainDate_subYearsClip(v_date_819_, v_years_820_);
lean_dec(v_years_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip(lean_object* v_dt_822_, lean_object* v_days_823_){
_start:
{
lean_object* v_year_824_; lean_object* v_month_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_849_; 
v_year_824_ = lean_ctor_get(v_dt_822_, 0);
v_month_825_ = lean_ctor_get(v_dt_822_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_dt_822_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_dt_822_, 2);
lean_dec(v_unused_850_);
v___x_827_ = v_dt_822_;
v_isShared_828_ = v_isSharedCheck_849_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_month_825_);
lean_inc(v_year_824_);
lean_dec(v_dt_822_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_849_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
uint8_t v___y_830_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_839_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_840_ = lean_int_mod(v_year_824_, v___x_839_);
v___x_841_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_842_ = lean_int_dec_eq(v___x_840_, v___x_841_);
lean_dec(v___x_840_);
if (v___x_842_ == 0)
{
v___y_830_ = v___x_842_;
goto v___jp_829_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_843_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_844_ = lean_int_mod(v_year_824_, v___x_843_);
v___x_845_ = lean_int_dec_eq(v___x_844_, v___x_841_);
lean_dec(v___x_844_);
if (v___x_845_ == 0)
{
v___y_830_ = v___x_842_;
goto v___jp_829_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_846_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_847_ = lean_int_mod(v_year_824_, v___x_846_);
v___x_848_ = lean_int_dec_eq(v___x_847_, v___x_841_);
lean_dec(v___x_847_);
v___y_830_ = v___x_848_;
goto v___jp_829_;
}
}
v___jp_829_:
{
lean_object* v_max_831_; uint8_t v___x_832_; 
v_max_831_ = l_Std_Time_Month_Ordinal_days(v___y_830_, v_month_825_);
v___x_832_ = lean_int_dec_lt(v_max_831_, v_days_823_);
if (v___x_832_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v_max_831_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 2, v_days_823_);
v___x_834_ = v___x_827_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_year_824_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_month_825_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_days_823_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
lean_object* v___x_837_; 
lean_dec(v_days_823_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 2, v_max_831_);
v___x_837_ = v___x_827_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_year_824_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_month_825_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_max_831_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver(lean_object* v_dt_851_, lean_object* v_days_852_){
_start:
{
lean_object* v_year_853_; lean_object* v_month_854_; lean_object* v___x_855_; 
v_year_853_ = lean_ctor_get(v_dt_851_, 0);
lean_inc(v_year_853_);
v_month_854_ = lean_ctor_get(v_dt_851_, 1);
lean_inc(v_month_854_);
lean_dec_ref(v_dt_851_);
v___x_855_ = l_Std_Time_PlainDate_rollOver(v_year_853_, v_month_854_, v_days_852_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver___boxed(lean_object* v_dt_856_, lean_object* v_days_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_Time_PlainDate_withDaysRollOver(v_dt_856_, v_days_857_);
lean_dec(v_days_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip(lean_object* v_dt_859_, lean_object* v_month_860_){
_start:
{
lean_object* v_year_861_; lean_object* v_day_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_886_; 
v_year_861_ = lean_ctor_get(v_dt_859_, 0);
v_day_862_ = lean_ctor_get(v_dt_859_, 2);
v_isSharedCheck_886_ = !lean_is_exclusive(v_dt_859_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_dt_859_, 1);
lean_dec(v_unused_887_);
v___x_864_ = v_dt_859_;
v_isShared_865_ = v_isSharedCheck_886_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_day_862_);
lean_inc(v_year_861_);
lean_dec(v_dt_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_886_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___y_867_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_876_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_877_ = lean_int_mod(v_year_861_, v___x_876_);
v___x_878_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_879_ = lean_int_dec_eq(v___x_877_, v___x_878_);
lean_dec(v___x_877_);
if (v___x_879_ == 0)
{
v___y_867_ = v___x_879_;
goto v___jp_866_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_880_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_881_ = lean_int_mod(v_year_861_, v___x_880_);
v___x_882_ = lean_int_dec_eq(v___x_881_, v___x_878_);
lean_dec(v___x_881_);
if (v___x_882_ == 0)
{
v___y_867_ = v___x_879_;
goto v___jp_866_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v___x_883_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_884_ = lean_int_mod(v_year_861_, v___x_883_);
v___x_885_ = lean_int_dec_eq(v___x_884_, v___x_878_);
lean_dec(v___x_884_);
v___y_867_ = v___x_885_;
goto v___jp_866_;
}
}
v___jp_866_:
{
lean_object* v_max_868_; uint8_t v___x_869_; 
v_max_868_ = l_Std_Time_Month_Ordinal_days(v___y_867_, v_month_860_);
v___x_869_ = lean_int_dec_lt(v_max_868_, v_day_862_);
if (v___x_869_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_max_868_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v_month_860_);
v___x_871_ = v___x_864_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_year_861_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_month_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_day_862_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v___x_874_; 
lean_dec(v_day_862_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 2, v_max_868_);
lean_ctor_set(v___x_864_, 1, v_month_860_);
v___x_874_ = v___x_864_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_year_861_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_month_860_);
lean_ctor_set(v_reuseFailAlloc_875_, 2, v_max_868_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthRollOver(lean_object* v_dt_888_, lean_object* v_month_889_){
_start:
{
lean_object* v_year_890_; lean_object* v_day_891_; lean_object* v___x_892_; 
v_year_890_ = lean_ctor_get(v_dt_888_, 0);
lean_inc(v_year_890_);
v_day_891_ = lean_ctor_get(v_dt_888_, 2);
lean_inc(v_day_891_);
lean_dec_ref(v_dt_888_);
v___x_892_ = l_Std_Time_PlainDate_rollOver(v_year_890_, v_month_889_, v_day_891_);
lean_dec(v_day_891_);
return v___x_892_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__0(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_894_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_895_ = lean_int_sub(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__1(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_range_898_; 
v___x_896_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_897_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__0, &l_Std_Time_PlainDate_weekday___closed__0_once, _init_l_Std_Time_PlainDate_weekday___closed__0);
v_range_898_ = lean_int_add(v___x_897_, v___x_896_);
return v_range_898_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__2(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_900_ = lean_int_neg(v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__3(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(6u);
v___x_902_ = lean_nat_to_int(v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_weekday(lean_object* v_date_903_){
_start:
{
lean_object* v___y_905_; lean_object* v_days_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_days_914_ = l_Std_Time_PlainDate_toEpochDay(v_date_903_);
v___x_915_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_916_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__2, &l_Std_Time_PlainDate_weekday___closed__2_once, _init_l_Std_Time_PlainDate_weekday___closed__2);
v___x_917_ = lean_int_dec_le(v___x_916_, v_days_914_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_918_ = lean_obj_once(&l_Std_Time_PlainDate_ofEpochDay___closed__8, &l_Std_Time_PlainDate_ofEpochDay___closed__8_once, _init_l_Std_Time_PlainDate_ofEpochDay___closed__8);
v___x_919_ = lean_int_add(v_days_914_, v___x_918_);
lean_dec(v_days_914_);
v___x_920_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_921_ = lean_int_emod(v___x_919_, v___x_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__3, &l_Std_Time_PlainDate_weekday___closed__3_once, _init_l_Std_Time_PlainDate_weekday___closed__3);
v___x_923_ = lean_int_add(v___x_921_, v___x_922_);
lean_dec(v___x_921_);
v___y_905_ = v___x_923_;
goto v___jp_904_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_int_add(v_days_914_, v___x_915_);
lean_dec(v_days_914_);
v___x_925_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_926_ = lean_int_emod(v___x_924_, v___x_925_);
lean_dec(v___x_924_);
v___y_905_ = v___x_926_;
goto v___jp_904_;
}
v___jp_904_:
{
lean_object* v___x_906_; lean_object* v_range_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_906_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_range_907_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__1, &l_Std_Time_PlainDate_weekday___closed__1_once, _init_l_Std_Time_PlainDate_weekday___closed__1);
v___x_908_ = lean_int_sub(v___y_905_, v___x_906_);
lean_dec(v___y_905_);
v___x_909_ = lean_int_emod(v___x_908_, v_range_907_);
lean_dec(v___x_908_);
v___x_910_ = lean_int_add(v___x_909_, v_range_907_);
lean_dec(v___x_909_);
v___x_911_ = lean_int_emod(v___x_910_, v_range_907_);
lean_dec(v___x_910_);
v___x_912_ = lean_int_add(v___x_911_, v___x_906_);
lean_dec(v___x_911_);
v___x_913_ = l_Std_Time_Weekday_ofOrdinal(v___x_912_);
lean_dec(v___x_912_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekday___boxed(lean_object* v_date_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Std_Time_PlainDate_weekday(v_date_927_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfMonth___closed__0(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_931_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__3, &l_Std_Time_PlainDate_weekday___closed__3_once, _init_l_Std_Time_PlainDate_weekday___closed__3);
v___x_932_ = lean_int_sub(v___x_931_, v___x_930_);
return v___x_932_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfMonth___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v_range_935_; 
v___x_933_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_934_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v_range_935_ = lean_int_add(v___x_934_, v___x_933_);
return v_range_935_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object* v_date_936_, uint8_t v_firstDay_937_){
_start:
{
lean_object* v_year_938_; lean_object* v_month_939_; lean_object* v_day_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_985_; 
v_year_938_ = lean_ctor_get(v_date_936_, 0);
v_month_939_ = lean_ctor_get(v_date_936_, 1);
v_day_940_ = lean_ctor_get(v_date_936_, 2);
v_isSharedCheck_985_ = !lean_is_exclusive(v_date_936_);
if (v_isSharedCheck_985_ == 0)
{
v___x_942_ = v_date_936_;
v_isShared_943_ = v_isSharedCheck_985_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_day_940_);
lean_inc(v_month_939_);
lean_inc(v_year_938_);
lean_dec(v_date_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_985_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___y_945_; lean_object* v___x_964_; uint8_t v___y_966_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_964_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_975_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_976_ = lean_int_mod(v_year_938_, v___x_975_);
v___x_977_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_978_ = lean_int_dec_eq(v___x_976_, v___x_977_);
lean_dec(v___x_976_);
if (v___x_978_ == 0)
{
v___y_966_ = v___x_978_;
goto v___jp_965_;
}
else
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_979_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_980_ = lean_int_mod(v_year_938_, v___x_979_);
v___x_981_ = lean_int_dec_eq(v___x_980_, v___x_977_);
lean_dec(v___x_980_);
if (v___x_981_ == 0)
{
v___y_966_ = v___x_978_;
goto v___jp_965_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_983_ = lean_int_mod(v_year_938_, v___x_982_);
v___x_984_ = lean_int_dec_eq(v___x_983_, v___x_977_);
lean_dec(v___x_983_);
v___y_966_ = v___x_984_;
goto v___jp_965_;
}
}
v___jp_944_:
{
uint8_t v___x_946_; lean_object* v_day1Ord_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_offset_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_range_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_946_ = l_Std_Time_PlainDate_weekday(v___y_945_);
v_day1Ord_947_ = l_Std_Time_Weekday_toOrdinal(v___x_946_);
v___x_948_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_937_);
v___x_949_ = lean_int_sub(v_day1Ord_947_, v___x_948_);
lean_dec(v___x_948_);
lean_dec(v_day1Ord_947_);
v___x_950_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_951_ = lean_int_add(v___x_949_, v___x_950_);
lean_dec(v___x_949_);
v_offset_952_ = lean_int_emod(v___x_951_, v___x_950_);
lean_dec(v___x_951_);
v___x_953_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_954_ = lean_int_sub(v_day_940_, v___x_953_);
lean_dec(v_day_940_);
v___x_955_ = lean_int_add(v___x_954_, v_offset_952_);
lean_dec(v_offset_952_);
lean_dec(v___x_954_);
v___x_956_ = lean_int_ediv(v___x_955_, v___x_950_);
lean_dec(v___x_955_);
v___x_957_ = lean_int_add(v___x_956_, v___x_953_);
lean_dec(v___x_956_);
v_range_958_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__1, &l_Std_Time_PlainDate_weekOfMonth___closed__1_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__1);
v___x_959_ = lean_int_sub(v___x_957_, v___x_953_);
lean_dec(v___x_957_);
v___x_960_ = lean_int_emod(v___x_959_, v_range_958_);
lean_dec(v___x_959_);
v___x_961_ = lean_int_add(v___x_960_, v_range_958_);
lean_dec(v___x_960_);
v___x_962_ = lean_int_emod(v___x_961_, v_range_958_);
lean_dec(v___x_961_);
v___x_963_ = lean_int_add(v___x_962_, v___x_953_);
lean_dec(v___x_962_);
return v___x_963_;
}
v___jp_965_:
{
lean_object* v_max_967_; uint8_t v___x_968_; 
v_max_967_ = l_Std_Time_Month_Ordinal_days(v___y_966_, v_month_939_);
v___x_968_ = lean_int_dec_lt(v_max_967_, v___x_964_);
if (v___x_968_ == 0)
{
lean_object* v___x_970_; 
lean_dec(v_max_967_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 2, v___x_964_);
v___x_970_ = v___x_942_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_year_938_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_month_939_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v___x_964_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v___y_945_ = v___x_970_;
goto v___jp_944_;
}
}
else
{
lean_object* v___x_973_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 2, v_max_967_);
v___x_973_ = v___x_942_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_year_938_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_month_939_);
lean_ctor_set(v_reuseFailAlloc_974_, 2, v_max_967_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
v___y_945_ = v___x_973_;
goto v___jp_944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object* v_date_986_, lean_object* v_firstDay_987_){
_start:
{
uint8_t v_firstDay_boxed_988_; lean_object* v_res_989_; 
v_firstDay_boxed_988_ = lean_unbox(v_firstDay_987_);
v_res_989_ = l_Std_Time_PlainDate_weekOfMonth(v_date_986_, v_firstDay_boxed_988_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday(lean_object* v_date_990_, uint8_t v_desiredWeekday_991_){
_start:
{
lean_object* v___y_993_; uint8_t v___x_997_; lean_object* v_weekday_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
lean_inc_ref(v_date_990_);
v___x_997_ = l_Std_Time_PlainDate_weekday(v_date_990_);
v_weekday_998_ = l_Std_Time_Weekday_toOrdinal(v___x_997_);
v___x_999_ = l_Std_Time_Weekday_toOrdinal(v_desiredWeekday_991_);
v___x_1000_ = lean_int_neg(v_weekday_998_);
lean_dec(v_weekday_998_);
v___x_1001_ = lean_int_add(v___x_999_, v___x_1000_);
lean_dec(v___x_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1003_ = lean_int_dec_lt(v___x_1001_, v___x_1002_);
if (v___x_1003_ == 0)
{
v___y_993_ = v___x_1001_;
goto v___jp_992_;
}
else
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1005_ = lean_int_add(v___x_1001_, v___x_1004_);
lean_dec(v___x_1001_);
v___y_993_ = v___x_1005_;
goto v___jp_992_;
}
v___jp_992_:
{
lean_object* v_dateDays_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_dateDays_994_ = l_Std_Time_PlainDate_toEpochDay(v_date_990_);
v___x_995_ = lean_int_add(v_dateDays_994_, v___y_993_);
lean_dec(v___y_993_);
lean_dec(v_dateDays_994_);
v___x_996_ = l_Std_Time_PlainDate_ofEpochDay(v___x_995_);
lean_dec(v___x_995_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object* v_date_1006_, lean_object* v_desiredWeekday_1007_){
_start:
{
uint8_t v_desiredWeekday_boxed_1008_; lean_object* v_res_1009_; 
v_desiredWeekday_boxed_1008_ = lean_unbox(v_desiredWeekday_1007_);
v_res_1009_ = l_Std_Time_PlainDate_withWeekday(v_date_1006_, v_desiredWeekday_boxed_1008_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(uint8_t v_weekday_1010_, uint8_t v_firstDay_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1012_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1013_ = l_Std_Time_Weekday_toOrdinal(v_weekday_1010_);
v___x_1014_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_1011_);
v___x_1015_ = lean_int_neg(v___x_1014_);
lean_dec(v___x_1014_);
v___x_1016_ = lean_int_add(v___x_1013_, v___x_1015_);
lean_dec(v___x_1015_);
lean_dec(v___x_1013_);
v___x_1017_ = lean_int_emod(v___x_1016_, v___x_1012_);
lean_dec(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek___boxed(lean_object* v_weekday_1018_, lean_object* v_firstDay_1019_){
_start:
{
uint8_t v_weekday_boxed_1020_; uint8_t v_firstDay_boxed_1021_; lean_object* v_res_1022_; 
v_weekday_boxed_1020_ = lean_unbox(v_weekday_1018_);
v_firstDay_boxed_1021_ = lean_unbox(v_firstDay_1019_);
v_res_1022_ = l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(v_weekday_boxed_1020_, v_firstDay_boxed_1021_);
return v_res_1022_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(11u);
v___x_1024_ = lean_nat_to_int(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__0);
v___x_1026_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1027_ = lean_int_add(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1029_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__1);
v___x_1030_ = lean_int_sub(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_range_1033_; 
v___x_1031_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1032_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__2);
v_range_1033_ = lean_int_add(v___x_1032_, v___x_1031_);
return v_range_1033_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4(void){
_start:
{
lean_object* v_range_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_range_1034_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1035_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_1036_ = lean_int_emod(v___x_1035_, v_range_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5(void){
_start:
{
lean_object* v_range_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_range_1037_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1038_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__4);
v___x_1039_ = lean_int_add(v___x_1038_, v_range_1037_);
return v___x_1039_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6(void){
_start:
{
lean_object* v_range_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_range_1040_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__3);
v___x_1041_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__5);
v___x_1042_ = lean_int_emod(v___x_1041_, v_range_1040_);
return v___x_1042_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1044_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__6);
v___x_1045_ = lean_int_add(v___x_1044_, v___x_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear(lean_object* v_year_1046_, uint8_t v_firstDay_1047_, lean_object* v_minimalDays_1048_){
_start:
{
lean_object* v___y_1050_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___y_1069_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1066_ = lean_obj_once(&l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7, &l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7_once, _init_l_Std_Time_PlainDate_startOfWeekBasedYear___closed__7);
v___x_1067_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_1074_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_1075_ = lean_int_mod(v_year_1046_, v___x_1074_);
v___x_1076_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1077_ = lean_int_dec_eq(v___x_1075_, v___x_1076_);
lean_dec(v___x_1075_);
if (v___x_1077_ == 0)
{
v___y_1069_ = v___x_1077_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_1079_ = lean_int_mod(v_year_1046_, v___x_1078_);
v___x_1080_ = lean_int_dec_eq(v___x_1079_, v___x_1076_);
lean_dec(v___x_1079_);
if (v___x_1080_ == 0)
{
v___y_1069_ = v___x_1077_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_1082_ = lean_int_mod(v_year_1046_, v___x_1081_);
v___x_1083_ = lean_int_dec_eq(v___x_1082_, v___x_1076_);
lean_dec(v___x_1082_);
v___y_1069_ = v___x_1083_;
goto v___jp_1068_;
}
}
v___jp_1049_:
{
uint8_t v___x_1051_; lean_object* v_localDay_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v_dateDays_1059_; lean_object* v___x_1060_; lean_object* v_weekStart_1061_; uint8_t v___x_1062_; 
lean_inc_ref(v___y_1050_);
v___x_1051_ = l_Std_Time_PlainDate_weekday(v___y_1050_);
v_localDay_1052_ = l___private_Std_Time_Date_PlainDate_0__Std_Time_PlainDate_localizedDayOfWeek(v___x_1051_, v_firstDay_1047_);
v___x_1053_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1054_ = lean_int_neg(v_localDay_1052_);
v___x_1055_ = lean_int_add(v___x_1053_, v___x_1054_);
lean_dec(v___x_1054_);
v___x_1056_ = l_Int_toNat(v_localDay_1052_);
lean_dec(v_localDay_1052_);
v___x_1057_ = lean_nat_to_int(v___x_1056_);
v___x_1058_ = lean_int_neg(v___x_1057_);
lean_dec(v___x_1057_);
v_dateDays_1059_ = l_Std_Time_PlainDate_toEpochDay(v___y_1050_);
v___x_1060_ = lean_int_add(v_dateDays_1059_, v___x_1058_);
lean_dec(v___x_1058_);
lean_dec(v_dateDays_1059_);
v_weekStart_1061_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1060_);
lean_dec(v___x_1060_);
v___x_1062_ = lean_int_dec_le(v_minimalDays_1048_, v___x_1055_);
lean_dec(v___x_1055_);
if (v___x_1062_ == 0)
{
lean_object* v_dateDays_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_dateDays_1063_ = l_Std_Time_PlainDate_toEpochDay(v_weekStart_1061_);
v___x_1064_ = lean_int_add(v_dateDays_1063_, v___x_1053_);
lean_dec(v_dateDays_1063_);
v___x_1065_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1064_);
lean_dec(v___x_1064_);
return v___x_1065_;
}
else
{
return v_weekStart_1061_;
}
}
v___jp_1068_:
{
lean_object* v_max_1070_; uint8_t v___x_1071_; 
v_max_1070_ = l_Std_Time_Month_Ordinal_days(v___y_1069_, v___x_1066_);
v___x_1071_ = lean_int_dec_lt(v_max_1070_, v___x_1067_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec(v_max_1070_);
v___x_1072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1072_, 0, v_year_1046_);
lean_ctor_set(v___x_1072_, 1, v___x_1066_);
lean_ctor_set(v___x_1072_, 2, v___x_1067_);
v___y_1050_ = v___x_1072_;
goto v___jp_1049_;
}
else
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1073_, 0, v_year_1046_);
lean_ctor_set(v___x_1073_, 1, v___x_1066_);
lean_ctor_set(v___x_1073_, 2, v_max_1070_);
v___y_1050_ = v___x_1073_;
goto v___jp_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_startOfWeekBasedYear___boxed(lean_object* v_year_1084_, lean_object* v_firstDay_1085_, lean_object* v_minimalDays_1086_){
_start:
{
uint8_t v_firstDay_boxed_1087_; lean_object* v_res_1088_; 
v_firstDay_boxed_1087_ = lean_unbox(v_firstDay_1085_);
v_res_1088_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1084_, v_firstDay_boxed_1087_, v_minimalDays_1086_);
lean_dec(v_minimalDays_1086_);
return v_res_1088_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__0(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_unsigned_to_nat(370u);
v___x_1090_ = lean_nat_to_int(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__1(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_1092_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__0, &l_Std_Time_PlainDate_weekOfYear___closed__0_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__0);
v___x_1093_ = lean_int_sub(v___x_1092_, v___x_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__2(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_range_1096_; 
v___x_1094_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1095_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__1, &l_Std_Time_PlainDate_weekOfYear___closed__1_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__1);
v_range_1096_ = lean_int_add(v___x_1095_, v___x_1094_);
return v_range_1096_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__3(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_unsigned_to_nat(52u);
v___x_1098_ = lean_nat_to_int(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__4(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__3, &l_Std_Time_PlainDate_weekOfYear___closed__3_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__3);
v___x_1100_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1101_ = lean_int_add(v___x_1100_, v___x_1099_);
return v___x_1101_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__5(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1103_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__4, &l_Std_Time_PlainDate_weekOfYear___closed__4_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__4);
v___x_1104_ = lean_int_sub(v___x_1103_, v___x_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__6(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v_range_1107_; 
v___x_1105_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1106_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__5, &l_Std_Time_PlainDate_weekOfYear___closed__5_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__5);
v_range_1107_ = lean_int_add(v___x_1106_, v___x_1105_);
return v_range_1107_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__7(void){
_start:
{
lean_object* v_range_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_range_1108_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1109_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_1110_ = lean_int_emod(v___x_1109_, v_range_1108_);
return v___x_1110_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__8(void){
_start:
{
lean_object* v_range_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_range_1111_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1112_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__7, &l_Std_Time_PlainDate_weekOfYear___closed__7_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__7);
v___x_1113_ = lean_int_add(v___x_1112_, v_range_1111_);
return v___x_1113_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__9(void){
_start:
{
lean_object* v_range_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v_range_1114_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__6, &l_Std_Time_PlainDate_weekOfYear___closed__6_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__6);
v___x_1115_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__8, &l_Std_Time_PlainDate_weekOfYear___closed__8_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__8);
v___x_1116_ = lean_int_emod(v___x_1115_, v_range_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfYear___closed__10(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1118_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__9, &l_Std_Time_PlainDate_weekOfYear___closed__9_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__9);
v___x_1119_ = lean_int_add(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object* v_date_1120_, uint8_t v_firstDay_1121_, lean_object* v_minDaysBounded_1122_){
_start:
{
lean_object* v_year_1123_; lean_object* v_thisYearStart_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_year_1123_ = lean_ctor_get(v_date_1120_, 0);
lean_inc_n(v_year_1123_, 2);
v_thisYearStart_1124_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1123_, v_firstDay_1121_, v_minDaysBounded_1122_);
v___x_1125_ = l_Std_Time_PlainDate_toEpochDay(v_date_1120_);
v___x_1126_ = l_Std_Time_PlainDate_toEpochDay(v_thisYearStart_1124_);
v___x_1127_ = lean_int_dec_lt(v___x_1125_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_nextYearStart_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1128_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1129_ = lean_int_add(v_year_1123_, v___x_1128_);
lean_dec(v_year_1123_);
v_nextYearStart_1130_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1129_, v_firstDay_1121_, v_minDaysBounded_1122_);
v___x_1131_ = l_Std_Time_PlainDate_toEpochDay(v_nextYearStart_1130_);
v___x_1132_ = lean_int_dec_le(v___x_1131_, v___x_1125_);
lean_dec(v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v_interval_1133_; lean_object* v___x_1134_; lean_object* v_range_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_interval_1133_ = lean_int_sub(v___x_1125_, v___x_1126_);
lean_dec(v___x_1126_);
lean_dec(v___x_1125_);
v___x_1134_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v_range_1135_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__2, &l_Std_Time_PlainDate_weekOfYear___closed__2_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__2);
v___x_1136_ = lean_int_sub(v_interval_1133_, v___x_1134_);
lean_dec(v_interval_1133_);
v___x_1137_ = lean_int_emod(v___x_1136_, v_range_1135_);
lean_dec(v___x_1136_);
v___x_1138_ = lean_int_add(v___x_1137_, v_range_1135_);
lean_dec(v___x_1137_);
v___x_1139_ = lean_int_emod(v___x_1138_, v_range_1135_);
lean_dec(v___x_1138_);
v___x_1140_ = lean_int_add(v___x_1139_, v___x_1134_);
lean_dec(v___x_1139_);
v___x_1141_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1142_ = lean_int_ediv(v___x_1140_, v___x_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_int_add(v___x_1142_, v___x_1128_);
lean_dec(v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
lean_dec(v___x_1126_);
lean_dec(v___x_1125_);
v___x_1144_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__10, &l_Std_Time_PlainDate_weekOfYear___closed__10_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__10);
return v___x_1144_;
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_prevYearStart_1147_; lean_object* v___x_1148_; lean_object* v_interval_1149_; lean_object* v___x_1150_; lean_object* v_range_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
lean_dec(v___x_1126_);
v___x_1145_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1146_ = lean_int_sub(v_year_1123_, v___x_1145_);
lean_dec(v_year_1123_);
v_prevYearStart_1147_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1146_, v_firstDay_1121_, v_minDaysBounded_1122_);
v___x_1148_ = l_Std_Time_PlainDate_toEpochDay(v_prevYearStart_1147_);
v_interval_1149_ = lean_int_sub(v___x_1125_, v___x_1148_);
lean_dec(v___x_1148_);
lean_dec(v___x_1125_);
v___x_1150_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v_range_1151_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfYear___closed__2, &l_Std_Time_PlainDate_weekOfYear___closed__2_once, _init_l_Std_Time_PlainDate_weekOfYear___closed__2);
v___x_1152_ = lean_int_sub(v_interval_1149_, v___x_1150_);
lean_dec(v_interval_1149_);
v___x_1153_ = lean_int_emod(v___x_1152_, v_range_1151_);
lean_dec(v___x_1152_);
v___x_1154_ = lean_int_add(v___x_1153_, v_range_1151_);
lean_dec(v___x_1153_);
v___x_1155_ = lean_int_emod(v___x_1154_, v_range_1151_);
lean_dec(v___x_1154_);
v___x_1156_ = lean_int_add(v___x_1155_, v___x_1150_);
lean_dec(v___x_1155_);
v___x_1157_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1158_ = lean_int_ediv(v___x_1156_, v___x_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_int_add(v___x_1158_, v___x_1145_);
lean_dec(v___x_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear___boxed(lean_object* v_date_1160_, lean_object* v_firstDay_1161_, lean_object* v_minDaysBounded_1162_){
_start:
{
uint8_t v_firstDay_boxed_1163_; lean_object* v_res_1164_; 
v_firstDay_boxed_1163_ = lean_unbox(v_firstDay_1161_);
v_res_1164_ = l_Std_Time_PlainDate_weekOfYear(v_date_1160_, v_firstDay_boxed_1163_, v_minDaysBounded_1162_);
lean_dec(v_minDaysBounded_1162_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekYear(lean_object* v_date_1165_, uint8_t v_firstDay_1166_, lean_object* v_minDays_1167_){
_start:
{
lean_object* v_year_1168_; lean_object* v_thisYearStart_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_year_1168_ = lean_ctor_get(v_date_1165_, 0);
lean_inc_n(v_year_1168_, 2);
v_thisYearStart_1169_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v_year_1168_, v_firstDay_1166_, v_minDays_1167_);
v___x_1170_ = l_Std_Time_PlainDate_toEpochDay(v_date_1165_);
v___x_1171_ = l_Std_Time_PlainDate_toEpochDay(v_thisYearStart_1169_);
v___x_1172_ = lean_int_dec_lt(v___x_1170_, v___x_1171_);
lean_dec(v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_nextYearStart_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1173_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1174_ = lean_int_add(v_year_1168_, v___x_1173_);
lean_inc(v___x_1174_);
v_nextYearStart_1175_ = l_Std_Time_PlainDate_startOfWeekBasedYear(v___x_1174_, v_firstDay_1166_, v_minDays_1167_);
v___x_1176_ = l_Std_Time_PlainDate_toEpochDay(v_nextYearStart_1175_);
v___x_1177_ = lean_int_dec_le(v___x_1176_, v___x_1170_);
lean_dec(v___x_1170_);
lean_dec(v___x_1176_);
if (v___x_1177_ == 0)
{
lean_dec(v___x_1174_);
return v_year_1168_;
}
else
{
lean_dec(v_year_1168_);
return v___x_1174_;
}
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v___x_1170_);
v___x_1178_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1179_ = lean_int_sub(v_year_1168_, v___x_1178_);
lean_dec(v_year_1168_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekYear___boxed(lean_object* v_date_1180_, lean_object* v_firstDay_1181_, lean_object* v_minDays_1182_){
_start:
{
uint8_t v_firstDay_boxed_1183_; lean_object* v_res_1184_; 
v_firstDay_boxed_1183_ = lean_unbox(v_firstDay_1181_);
v_res_1184_ = l_Std_Time_PlainDate_weekYear(v_date_1180_, v_firstDay_boxed_1183_, v_minDays_1182_);
lean_dec(v_minDays_1182_);
return v_res_1184_;
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
