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
extern lean_object* l_Std_Time_Day_instOrdOrdinal;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Time_Month_instOrdOrdinal;
lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__3 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__3_value;
static const lean_closure_object l_Std_Time_instOrdPlainDate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__3_value),((lean_object*)&l_Std_Time_instOrdPlainDate___closed__0_value)} };
static const lean_object* l_Std_Time_instOrdPlainDate___closed__4 = (const lean_object*)&l_Std_Time_instOrdPlainDate___closed__4_value;
static lean_once_cell_t l_Std_Time_instOrdPlainDate___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainDate___closed__5;
static lean_once_cell_t l_Std_Time_instOrdPlainDate___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainDate___closed__6;
static lean_once_cell_t l_Std_Time_instOrdPlainDate___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainDate___closed__7;
static lean_once_cell_t l_Std_Time_instOrdPlainDate___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainDate___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainDate;
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
lean_object* v_year_47_; lean_object* v_month_48_; lean_object* v_day_49_; lean_object* v___x_50_; lean_object* v___y_52_; lean_object* v___y_53_; lean_object* v___y_54_; uint8_t v___y_55_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___y_89_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
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
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___y_52_);
lean_ctor_set(v___x_58_, 1, v___y_57_);
v___x_59_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v___y_55_);
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___y_56_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
lean_inc(v___y_53_);
v___x_61_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___y_53_);
lean_inc(v___y_54_);
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
v___x_68_ = l_Std_Time_Internal_Bounded_instRepr___lam__0(v_day_49_, v___x_67_);
v___x_69_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_66_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___y_55_);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_65_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___y_53_);
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
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___y_55_);
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
v___y_52_ = v___x_101_;
v___y_53_ = v___x_94_;
v___y_54_ = v___x_96_;
v___y_55_ = v___x_91_;
v___y_56_ = v___x_100_;
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
v___y_52_ = v___x_101_;
v___y_53_ = v___x_94_;
v___y_54_ = v___x_96_;
v___y_55_ = v___x_91_;
v___y_56_ = v___x_100_;
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
static lean_object* _init_l_Std_Time_instOrdPlainDate___closed__5(void){
_start:
{
lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___f_224_ = ((lean_object*)(l_Std_Time_instOrdPlainDate___closed__1));
v___x_225_ = l_Std_Time_Month_instOrdOrdinal;
v___x_226_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_226_, 0, lean_box(0));
lean_closure_set(v___x_226_, 1, lean_box(0));
lean_closure_set(v___x_226_, 2, v___x_225_);
lean_closure_set(v___x_226_, 3, v___f_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDate___closed__6(void){
_start:
{
lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___f_227_ = ((lean_object*)(l_Std_Time_instOrdPlainDate___closed__2));
v___x_228_ = l_Std_Time_Day_instOrdOrdinal;
v___x_229_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, lean_box(0));
lean_closure_set(v___x_229_, 2, v___x_228_);
lean_closure_set(v___x_229_, 3, v___f_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDate___closed__7(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Std_Time_instOrdPlainDate___closed__6, &l_Std_Time_instOrdPlainDate___closed__6_once, _init_l_Std_Time_instOrdPlainDate___closed__6);
v___x_231_ = lean_obj_once(&l_Std_Time_instOrdPlainDate___closed__5, &l_Std_Time_instOrdPlainDate___closed__5_once, _init_l_Std_Time_instOrdPlainDate___closed__5);
v___x_232_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_232_, 0, lean_box(0));
lean_closure_set(v___x_232_, 1, lean_box(0));
lean_closure_set(v___x_232_, 2, v___x_231_);
lean_closure_set(v___x_232_, 3, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDate___closed__8(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l_Std_Time_instOrdPlainDate___closed__7, &l_Std_Time_instOrdPlainDate___closed__7_once, _init_l_Std_Time_instOrdPlainDate___closed__7);
v___x_234_ = ((lean_object*)(l_Std_Time_instOrdPlainDate___closed__4));
v___x_235_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_235_, 0, lean_box(0));
lean_closure_set(v___x_235_, 1, lean_box(0));
lean_closure_set(v___x_235_, 2, v___x_234_);
lean_closure_set(v___x_235_, 3, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainDate(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Std_Time_instOrdPlainDate___closed__8, &l_Std_Time_instOrdPlainDate___closed__8_once, _init_l_Std_Time_instOrdPlainDate___closed__8);
return v___x_236_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_unsigned_to_nat(4u);
v___x_238_ = lean_nat_to_int(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(400u);
v___x_240_ = lean_nat_to_int(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(100u);
v___x_242_ = lean_nat_to_int(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDayClip(lean_object* v_year_243_, lean_object* v_month_244_, lean_object* v_day_245_){
_start:
{
uint8_t v___y_247_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_259_; 
v___x_252_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_253_ = lean_int_mod(v_year_243_, v___x_252_);
v___x_254_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_259_ = lean_int_dec_eq(v___x_253_, v___x_254_);
lean_dec(v___x_253_);
if (v___x_259_ == 0)
{
v___y_247_ = v___x_259_;
goto v___jp_246_;
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_260_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_261_ = lean_int_mod(v_year_243_, v___x_260_);
v___x_262_ = lean_int_dec_eq(v___x_261_, v___x_254_);
lean_dec(v___x_261_);
if (v___x_262_ == 0)
{
if (v___x_259_ == 0)
{
goto v___jp_255_;
}
else
{
v___y_247_ = v___x_259_;
goto v___jp_246_;
}
}
else
{
goto v___jp_255_;
}
}
v___jp_246_:
{
lean_object* v_max_248_; uint8_t v___x_249_; 
v_max_248_ = l_Std_Time_Month_Ordinal_days(v___y_247_, v_month_244_);
v___x_249_ = lean_int_dec_lt(v_max_248_, v_day_245_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v_max_248_);
v___x_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_250_, 0, v_year_243_);
lean_ctor_set(v___x_250_, 1, v_month_244_);
lean_ctor_set(v___x_250_, 2, v_day_245_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
lean_dec(v_day_245_);
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v_year_243_);
lean_ctor_set(v___x_251_, 1, v_month_244_);
lean_ctor_set(v___x_251_, 2, v_max_248_);
return v___x_251_;
}
}
v___jp_255_:
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_257_ = lean_int_mod(v_year_243_, v___x_256_);
v___x_258_ = lean_int_dec_eq(v___x_257_, v___x_254_);
lean_dec(v___x_257_);
v___y_247_ = v___x_258_;
goto v___jp_246_;
}
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_263_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__17, &l_Std_Time_instInhabitedPlainDate___closed__17_once, _init_l_Std_Time_instInhabitedPlainDate___closed__17);
v___x_264_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__9, &l_Std_Time_instInhabitedPlainDate___closed__9_once, _init_l_Std_Time_instInhabitedPlainDate___closed__9);
v___x_265_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___x_264_);
lean_ctor_set(v___x_266_, 2, v___x_263_);
return v___x_266_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instInhabited(void){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_Std_Time_PlainDate_instInhabited___closed__0, &l_Std_Time_PlainDate_instInhabited___closed__0_once, _init_l_Std_Time_PlainDate_instInhabited___closed__0);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearMonthDay_x3f(lean_object* v_year_268_, lean_object* v_month_269_, lean_object* v_day_270_){
_start:
{
uint8_t v___y_272_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_285_; 
v___x_278_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_279_ = lean_int_mod(v_year_268_, v___x_278_);
v___x_280_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_285_ = lean_int_dec_eq(v___x_279_, v___x_280_);
lean_dec(v___x_279_);
if (v___x_285_ == 0)
{
v___y_272_ = v___x_285_;
goto v___jp_271_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_286_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_287_ = lean_int_mod(v_year_268_, v___x_286_);
v___x_288_ = lean_int_dec_eq(v___x_287_, v___x_280_);
lean_dec(v___x_287_);
if (v___x_288_ == 0)
{
if (v___x_285_ == 0)
{
goto v___jp_281_;
}
else
{
v___y_272_ = v___x_285_;
goto v___jp_271_;
}
}
else
{
goto v___jp_281_;
}
}
v___jp_271_:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = l_Std_Time_Month_Ordinal_days(v___y_272_, v_month_269_);
v___x_274_ = lean_int_dec_le(v_day_270_, v___x_273_);
lean_dec(v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec(v_day_270_);
lean_dec(v_month_269_);
lean_dec(v_year_268_);
v___x_275_ = lean_box(0);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v_year_268_);
lean_ctor_set(v___x_276_, 1, v_month_269_);
lean_ctor_set(v___x_276_, 2, v_day_270_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
v___jp_281_:
{
lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_282_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_283_ = lean_int_mod(v_year_268_, v___x_282_);
v___x_284_ = lean_int_dec_eq(v___x_283_, v___x_280_);
lean_dec(v___x_283_);
v___y_272_ = v___x_284_;
goto v___jp_271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal(lean_object* v_year_289_, lean_object* v_ordinal_290_){
_start:
{
uint8_t v___y_292_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_304_; 
v___x_297_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_298_ = lean_int_mod(v_year_289_, v___x_297_);
v___x_299_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_304_ = lean_int_dec_eq(v___x_298_, v___x_299_);
lean_dec(v___x_298_);
if (v___x_304_ == 0)
{
v___y_292_ = v___x_304_;
goto v___jp_291_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_306_ = lean_int_mod(v_year_289_, v___x_305_);
v___x_307_ = lean_int_dec_eq(v___x_306_, v___x_299_);
lean_dec(v___x_306_);
if (v___x_307_ == 0)
{
if (v___x_304_ == 0)
{
goto v___jp_300_;
}
else
{
v___y_292_ = v___x_304_;
goto v___jp_291_;
}
}
else
{
goto v___jp_300_;
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
v___jp_300_:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_302_ = lean_int_mod(v_year_289_, v___x_301_);
v___x_303_ = lean_int_dec_eq(v___x_302_, v___x_299_);
lean_dec(v___x_302_);
v___y_292_ = v___x_303_;
goto v___jp_291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofYearOrdinal___boxed(lean_object* v_year_308_, lean_object* v_ordinal_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Time_PlainDate_ofYearOrdinal(v_year_308_, v_ordinal_309_);
lean_dec(v_ordinal_309_);
return v_res_310_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(719468u);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(31u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(12u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(146097u);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1460u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(36524u);
v___x_322_ = lean_nat_to_int(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(146096u);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(365u);
v___x_326_ = lean_nat_to_int(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(5u);
v___x_328_ = lean_nat_to_int(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(2u);
v___x_330_ = lean_nat_to_int(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(153u);
v___x_332_ = lean_nat_to_int(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(10u);
v___x_334_ = lean_nat_to_int(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___x_336_ = lean_int_neg(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(3u);
v___x_338_ = lean_nat_to_int(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object* v_day_339_){
_start:
{
lean_object* v___y_341_; lean_object* v___y_342_; lean_object* v___y_343_; uint8_t v___y_344_; lean_object* v___x_349_; lean_object* v_z_350_; lean_object* v___x_351_; lean_object* v___y_353_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v___y_362_; lean_object* v___y_363_; lean_object* v___y_364_; lean_object* v___y_365_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___y_377_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; lean_object* v___y_389_; lean_object* v___y_395_; lean_object* v___y_396_; lean_object* v___y_397_; lean_object* v___y_398_; lean_object* v___y_399_; lean_object* v___y_400_; lean_object* v___y_401_; lean_object* v___y_402_; lean_object* v___y_403_; lean_object* v___y_407_; uint8_t v___x_450_; 
v___x_349_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0);
v_z_350_ = lean_int_add(v_day_339_, v___x_349_);
v___x_351_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_450_ = lean_int_dec_le(v___x_351_, v_z_350_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6);
v___x_452_ = lean_int_sub(v_z_350_, v___x_451_);
v___y_407_ = v___x_452_;
goto v___jp_406_;
}
else
{
lean_inc(v_z_350_);
v___y_407_ = v_z_350_;
goto v___jp_406_;
}
v___jp_340_:
{
lean_object* v_max_345_; uint8_t v___x_346_; 
v_max_345_ = l_Std_Time_Month_Ordinal_days(v___y_344_, v___y_341_);
v___x_346_ = lean_int_dec_lt(v_max_345_, v___y_342_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_dec(v_max_345_);
v___x_347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_347_, 0, v___y_343_);
lean_ctor_set(v___x_347_, 1, v___y_341_);
lean_ctor_set(v___x_347_, 2, v___y_342_);
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
lean_dec(v___y_342_);
v___x_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_348_, 0, v___y_343_);
lean_ctor_set(v___x_348_, 1, v___y_341_);
lean_ctor_set(v___x_348_, 2, v_max_345_);
return v___x_348_;
}
}
v___jp_352_:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_int_mod(v___y_356_, v___y_353_);
lean_dec(v___y_353_);
v___x_358_ = lean_int_dec_eq(v___x_357_, v___x_351_);
lean_dec(v___x_357_);
v___y_341_ = v___y_354_;
v___y_342_ = v___y_355_;
v___y_343_ = v___y_356_;
v___y_344_ = v___x_358_;
goto v___jp_340_;
}
v___jp_359_:
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_int_mod(v___y_364_, v___y_361_);
lean_dec(v___y_361_);
v___x_367_ = lean_int_dec_eq(v___x_366_, v___x_351_);
lean_dec(v___x_366_);
if (v___x_367_ == 0)
{
lean_dec(v___y_363_);
lean_dec(v___y_360_);
v___y_341_ = v___y_362_;
v___y_342_ = v___y_365_;
v___y_343_ = v___y_364_;
v___y_344_ = v___x_367_;
goto v___jp_340_;
}
else
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_int_mod(v___y_364_, v___y_363_);
lean_dec(v___y_363_);
v___x_369_ = lean_int_dec_eq(v___x_368_, v___x_351_);
lean_dec(v___x_368_);
if (v___x_369_ == 0)
{
if (v___x_367_ == 0)
{
v___y_353_ = v___y_360_;
v___y_354_ = v___y_362_;
v___y_355_ = v___y_365_;
v___y_356_ = v___y_364_;
goto v___jp_352_;
}
else
{
lean_dec(v___y_360_);
v___y_341_ = v___y_362_;
v___y_342_ = v___y_365_;
v___y_343_ = v___y_364_;
v___y_344_ = v___x_367_;
goto v___jp_340_;
}
}
else
{
v___y_353_ = v___y_360_;
v___y_354_ = v___y_362_;
v___y_355_ = v___y_365_;
v___y_356_ = v___y_364_;
goto v___jp_352_;
}
}
}
v___jp_370_:
{
uint8_t v___x_378_; 
v___x_378_ = lean_int_dec_le(v___y_373_, v___y_376_);
if (v___x_378_ == 0)
{
lean_dec(v___y_376_);
v___y_360_ = v___y_372_;
v___y_361_ = v___y_371_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_375_;
v___y_364_ = v___y_374_;
v___y_365_ = v___y_373_;
goto v___jp_359_;
}
else
{
lean_object* v___x_379_; uint8_t v___x_380_; 
lean_dec(v___y_373_);
v___x_379_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__1);
v___x_380_ = lean_int_dec_le(v___y_376_, v___x_379_);
if (v___x_380_ == 0)
{
lean_dec(v___y_376_);
v___y_360_ = v___y_372_;
v___y_361_ = v___y_371_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_375_;
v___y_364_ = v___y_374_;
v___y_365_ = v___x_379_;
goto v___jp_359_;
}
else
{
v___y_360_ = v___y_372_;
v___y_361_ = v___y_371_;
v___y_362_ = v___y_377_;
v___y_363_ = v___y_375_;
v___y_364_ = v___y_374_;
v___y_365_ = v___y_376_;
goto v___jp_359_;
}
}
}
v___jp_381_:
{
lean_object* v_y_390_; uint8_t v___x_391_; 
v_y_390_ = lean_int_add(v___y_386_, v___y_389_);
lean_dec(v___y_389_);
lean_dec(v___y_386_);
v___x_391_ = lean_int_dec_le(v___y_385_, v___y_382_);
if (v___x_391_ == 0)
{
lean_dec(v___y_382_);
lean_inc(v___y_385_);
v___y_371_ = v___y_384_;
v___y_372_ = v___y_383_;
v___y_373_ = v___y_385_;
v___y_374_ = v_y_390_;
v___y_375_ = v___y_387_;
v___y_376_ = v___y_388_;
v___y_377_ = v___y_385_;
goto v___jp_370_;
}
else
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_393_ = lean_int_dec_le(v___y_382_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v___y_382_);
v___y_371_ = v___y_384_;
v___y_372_ = v___y_383_;
v___y_373_ = v___y_385_;
v___y_374_ = v_y_390_;
v___y_375_ = v___y_387_;
v___y_376_ = v___y_388_;
v___y_377_ = v___x_392_;
goto v___jp_370_;
}
else
{
v___y_371_ = v___y_384_;
v___y_372_ = v___y_383_;
v___y_373_ = v___y_385_;
v___y_374_ = v_y_390_;
v___y_375_ = v___y_387_;
v___y_376_ = v___y_388_;
v___y_377_ = v___y_382_;
goto v___jp_370_;
}
}
}
v___jp_394_:
{
lean_object* v_m_404_; uint8_t v___x_405_; 
v_m_404_ = lean_int_add(v___y_398_, v___y_403_);
lean_dec(v___y_403_);
lean_dec(v___y_398_);
v___x_405_ = lean_int_dec_le(v_m_404_, v___y_399_);
lean_dec(v___y_399_);
if (v___x_405_ == 0)
{
v___y_382_ = v_m_404_;
v___y_383_ = v___y_396_;
v___y_384_ = v___y_395_;
v___y_385_ = v___y_397_;
v___y_386_ = v___y_400_;
v___y_387_ = v___y_401_;
v___y_388_ = v___y_402_;
v___y_389_ = v___x_351_;
goto v___jp_381_;
}
else
{
lean_inc(v___y_397_);
v___y_382_ = v_m_404_;
v___y_383_ = v___y_396_;
v___y_384_ = v___y_395_;
v___y_385_ = v___y_397_;
v___y_386_ = v___y_400_;
v___y_387_ = v___y_401_;
v___y_388_ = v___y_402_;
v___y_389_ = v___y_397_;
goto v___jp_381_;
}
}
v___jp_406_:
{
lean_object* v___x_408_; lean_object* v_era_409_; lean_object* v___x_410_; lean_object* v_doe_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_yoe_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_y_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_doy_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_mp_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_d_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_408_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3);
v_era_409_ = lean_int_div(v___y_407_, v___x_408_);
lean_dec(v___y_407_);
v___x_410_ = lean_int_mul(v_era_409_, v___x_408_);
v_doe_411_ = lean_int_sub(v_z_350_, v___x_410_);
lean_dec(v___x_410_);
lean_dec(v_z_350_);
v___x_412_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__4);
v___x_413_ = lean_int_div(v_doe_411_, v___x_412_);
v___x_414_ = lean_int_sub(v_doe_411_, v___x_413_);
lean_dec(v___x_413_);
v___x_415_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__5);
v___x_416_ = lean_int_div(v_doe_411_, v___x_415_);
v___x_417_ = lean_int_add(v___x_414_, v___x_416_);
lean_dec(v___x_416_);
lean_dec(v___x_414_);
v___x_418_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__6);
v___x_419_ = lean_int_div(v_doe_411_, v___x_418_);
v___x_420_ = lean_int_sub(v___x_417_, v___x_419_);
lean_dec(v___x_419_);
lean_dec(v___x_417_);
v___x_421_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7);
v_yoe_422_ = lean_int_div(v___x_420_, v___x_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_424_ = lean_int_mul(v_era_409_, v___x_423_);
lean_dec(v_era_409_);
v_y_425_ = lean_int_add(v_yoe_422_, v___x_424_);
lean_dec(v___x_424_);
v___x_426_ = lean_int_mul(v___x_421_, v_yoe_422_);
v___x_427_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_428_ = lean_int_div(v_yoe_422_, v___x_427_);
v___x_429_ = lean_int_add(v___x_426_, v___x_428_);
lean_dec(v___x_428_);
lean_dec(v___x_426_);
v___x_430_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_431_ = lean_int_div(v_yoe_422_, v___x_430_);
lean_dec(v_yoe_422_);
v___x_432_ = lean_int_sub(v___x_429_, v___x_431_);
lean_dec(v___x_431_);
lean_dec(v___x_429_);
v_doy_433_ = lean_int_sub(v_doe_411_, v___x_432_);
lean_dec(v___x_432_);
lean_dec(v_doe_411_);
v___x_434_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8);
v___x_435_ = lean_int_mul(v___x_434_, v_doy_433_);
v___x_436_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9);
v___x_437_ = lean_int_add(v___x_435_, v___x_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10);
v_mp_439_ = lean_int_div(v___x_437_, v___x_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_int_mul(v___x_438_, v_mp_439_);
v___x_441_ = lean_int_add(v___x_440_, v___x_436_);
lean_dec(v___x_440_);
v___x_442_ = lean_int_div(v___x_441_, v___x_434_);
lean_dec(v___x_441_);
v___x_443_ = lean_int_sub(v_doy_433_, v___x_442_);
lean_dec(v___x_442_);
lean_dec(v_doy_433_);
v___x_444_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_d_445_ = lean_int_add(v___x_443_, v___x_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11);
v___x_447_ = lean_int_dec_lt(v_mp_439_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
v___x_448_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__12);
v___y_395_ = v___x_427_;
v___y_396_ = v___x_423_;
v___y_397_ = v___x_444_;
v___y_398_ = v_mp_439_;
v___y_399_ = v___x_436_;
v___y_400_ = v_y_425_;
v___y_401_ = v___x_430_;
v___y_402_ = v_d_445_;
v___y_403_ = v___x_448_;
goto v___jp_394_;
}
else
{
lean_object* v___x_449_; 
v___x_449_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13);
v___y_395_ = v___x_427_;
v___y_396_ = v___x_423_;
v___y_397_ = v___x_444_;
v___y_398_ = v_mp_439_;
v___y_399_ = v___x_436_;
v___y_400_ = v_y_425_;
v___y_401_ = v___x_430_;
v___y_402_ = v_d_445_;
v___y_403_ = v___x_449_;
goto v___jp_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___boxed(lean_object* v_day_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v_day_453_);
lean_dec(v_day_453_);
return v_res_454_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekOfMonth___closed__0(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_456_ = lean_int_neg(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object* v_date_457_){
_start:
{
lean_object* v_day_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_day_458_ = lean_ctor_get(v_date_457_, 2);
v___x_459_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_460_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_461_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v___x_462_ = lean_int_add(v_day_458_, v___x_461_);
v___x_463_ = lean_int_ediv(v___x_462_, v___x_460_);
lean_dec(v___x_462_);
v___x_464_ = lean_int_add(v___x_463_, v___x_459_);
lean_dec(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfMonth___boxed(lean_object* v_date_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_Time_PlainDate_weekOfMonth(v_date_465_);
lean_dec_ref(v_date_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter(lean_object* v_date_467_){
_start:
{
lean_object* v_month_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_month_468_ = lean_ctor_get(v_date_467_, 1);
v___x_469_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_470_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13);
v___x_471_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v___x_472_ = lean_int_add(v_month_468_, v___x_471_);
v___x_473_ = lean_int_ediv(v___x_472_, v___x_470_);
lean_dec(v___x_472_);
v___x_474_ = lean_int_add(v___x_473_, v___x_469_);
lean_dec(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_quarter___boxed(lean_object* v_date_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_Time_PlainDate_quarter(v_date_475_);
lean_dec_ref(v_date_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object* v_date_477_){
_start:
{
lean_object* v_year_478_; lean_object* v_month_479_; lean_object* v_day_480_; uint8_t v___y_482_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_492_; 
v_year_478_ = lean_ctor_get(v_date_477_, 0);
v_month_479_ = lean_ctor_get(v_date_477_, 1);
v_day_480_ = lean_ctor_get(v_date_477_, 2);
v___x_485_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_486_ = lean_int_mod(v_year_478_, v___x_485_);
v___x_487_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_492_ = lean_int_dec_eq(v___x_486_, v___x_487_);
lean_dec(v___x_486_);
if (v___x_492_ == 0)
{
v___y_482_ = v___x_492_;
goto v___jp_481_;
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_493_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_494_ = lean_int_mod(v_year_478_, v___x_493_);
v___x_495_ = lean_int_dec_eq(v___x_494_, v___x_487_);
lean_dec(v___x_494_);
if (v___x_495_ == 0)
{
if (v___x_492_ == 0)
{
goto v___jp_488_;
}
else
{
v___y_482_ = v___x_492_;
goto v___jp_481_;
}
}
else
{
goto v___jp_488_;
}
}
v___jp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
lean_inc(v_day_480_);
lean_inc(v_month_479_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v_month_479_);
lean_ctor_set(v___x_483_, 1, v_day_480_);
v___x_484_ = l_Std_Time_ValidDate_dayOfYear(v___y_482_, v___x_483_);
lean_dec_ref(v___x_483_);
return v___x_484_;
}
v___jp_488_:
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_489_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_490_ = lean_int_mod(v_year_478_, v___x_489_);
v___x_491_ = lean_int_dec_eq(v___x_490_, v___x_487_);
lean_dec(v___x_490_);
v___y_482_ = v___x_491_;
goto v___jp_481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_dayOfYear___boxed(lean_object* v_date_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Time_PlainDate_dayOfYear(v_date_496_);
lean_dec_ref(v_date_496_);
return v_res_497_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_era(lean_object* v_date_498_){
_start:
{
lean_object* v_year_499_; uint8_t v___x_500_; 
v_year_499_ = lean_ctor_get(v_date_498_, 0);
v___x_500_ = l_Std_Time_Year_Offset_era(v_year_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_era___boxed(lean_object* v_date_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Std_Time_PlainDate_era(v_date_501_);
lean_dec_ref(v_date_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_inLeapYear(lean_object* v_date_504_){
_start:
{
lean_object* v_year_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_513_; 
v_year_505_ = lean_ctor_get(v_date_504_, 0);
v___x_506_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_507_ = lean_int_mod(v_year_505_, v___x_506_);
v___x_508_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_513_ = lean_int_dec_eq(v___x_507_, v___x_508_);
lean_dec(v___x_507_);
if (v___x_513_ == 0)
{
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_514_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_515_ = lean_int_mod(v_year_505_, v___x_514_);
v___x_516_ = lean_int_dec_eq(v___x_515_, v___x_508_);
lean_dec(v___x_515_);
if (v___x_516_ == 0)
{
if (v___x_513_ == 0)
{
goto v___jp_509_;
}
else
{
return v___x_513_;
}
}
else
{
goto v___jp_509_;
}
}
v___jp_509_:
{
lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_510_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_511_ = lean_int_mod(v_year_505_, v___x_510_);
v___x_512_ = lean_int_dec_eq(v___x_511_, v___x_508_);
lean_dec(v___x_511_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_inLeapYear___boxed(lean_object* v_date_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l_Std_Time_PlainDate_inLeapYear(v_date_517_);
lean_dec_ref(v_date_517_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__13);
v___x_521_ = lean_int_neg(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(399u);
v___x_523_ = lean_nat_to_int(v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object* v_date_524_){
_start:
{
lean_object* v_year_525_; lean_object* v_month_526_; lean_object* v_day_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_568_; uint8_t v___x_573_; 
v_year_525_ = lean_ctor_get(v_date_524_, 0);
lean_inc(v_year_525_);
v_month_526_ = lean_ctor_get(v_date_524_, 1);
lean_inc(v_month_526_);
v_day_527_ = lean_ctor_get(v_date_524_, 2);
lean_inc(v_day_527_);
lean_dec_ref(v_date_524_);
v___x_528_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__9);
v___x_529_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_573_ = lean_int_dec_lt(v___x_528_, v_month_526_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; 
v___x_574_ = lean_int_sub(v_year_525_, v___x_529_);
lean_dec(v_year_525_);
v___y_568_ = v___x_574_;
goto v___jp_567_;
}
else
{
v___y_568_ = v_year_525_;
goto v___jp_567_;
}
v___jp_530_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_doy_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v_doe_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_535_ = lean_int_add(v_month_526_, v___y_534_);
lean_dec(v___y_534_);
lean_dec(v_month_526_);
v___x_536_ = lean_int_mul(v___y_532_, v___x_535_);
lean_dec(v___x_535_);
lean_dec(v___y_532_);
v___x_537_ = lean_int_add(v___x_536_, v___x_528_);
lean_dec(v___x_536_);
v___x_538_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8);
v___x_539_ = lean_int_div(v___x_537_, v___x_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_int_add(v___x_539_, v_day_527_);
lean_dec(v_day_527_);
lean_dec(v___x_539_);
v_doy_541_ = lean_int_sub(v___x_540_, v___x_529_);
lean_dec(v___x_540_);
v___x_542_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__7);
v___x_543_ = lean_int_mul(v___y_531_, v___x_542_);
v___x_544_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_545_ = lean_int_div(v___y_531_, v___x_544_);
v___x_546_ = lean_int_add(v___x_543_, v___x_545_);
lean_dec(v___x_545_);
lean_dec(v___x_543_);
v___x_547_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_548_ = lean_int_div(v___y_531_, v___x_547_);
lean_dec(v___y_531_);
v___x_549_ = lean_int_sub(v___x_546_, v___x_548_);
lean_dec(v___x_548_);
lean_dec(v___x_546_);
v_doe_550_ = lean_int_add(v___x_549_, v_doy_541_);
lean_dec(v_doy_541_);
lean_dec(v___x_549_);
v___x_551_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__3);
v___x_552_ = lean_int_mul(v___y_533_, v___x_551_);
lean_dec(v___y_533_);
v___x_553_ = lean_int_add(v___x_552_, v_doe_550_);
lean_dec(v_doe_550_);
lean_dec(v___x_552_);
v___x_554_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__0);
v___x_555_ = lean_int_sub(v___x_553_, v___x_554_);
lean_dec(v___x_553_);
return v___x_555_;
}
v___jp_556_:
{
lean_object* v___x_559_; lean_object* v_era_560_; lean_object* v___x_561_; lean_object* v_yoe_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_559_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v_era_560_ = lean_int_div(v___y_558_, v___x_559_);
lean_dec(v___y_558_);
v___x_561_ = lean_int_mul(v_era_560_, v___x_559_);
v_yoe_562_ = lean_int_sub(v___y_557_, v___x_561_);
lean_dec(v___x_561_);
lean_dec(v___y_557_);
v___x_563_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__10);
v___x_564_ = lean_int_dec_lt(v___x_528_, v_month_526_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__24, &l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24);
v___y_531_ = v_yoe_562_;
v___y_532_ = v___x_563_;
v___y_533_ = v_era_560_;
v___y_534_ = v___x_565_;
goto v___jp_530_;
}
else
{
lean_object* v___x_566_; 
v___x_566_ = lean_obj_once(&l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0, &l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0_once, _init_l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__0);
v___y_531_ = v_yoe_562_;
v___y_532_ = v___x_563_;
v___y_533_ = v_era_560_;
v___y_534_ = v___x_566_;
goto v___jp_530_;
}
}
v___jp_567_:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_570_ = lean_int_dec_le(v___x_569_, v___y_568_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = lean_obj_once(&l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1, &l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1_once, _init_l_Std_Time_PlainDate_toDaysSinceUNIXEpoch___closed__1);
v___x_572_ = lean_int_sub(v___y_568_, v___x_571_);
v___y_557_ = v___y_568_;
v___y_558_ = v___x_572_;
goto v___jp_556_;
}
else
{
lean_inc(v___y_568_);
v___y_557_ = v___y_568_;
v___y_558_ = v___y_568_;
goto v___jp_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays(lean_object* v_date_575_, lean_object* v_days_576_){
_start:
{
lean_object* v_dateDays_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_dateDays_577_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_575_);
v___x_578_ = lean_int_add(v_dateDays_577_, v_days_576_);
lean_dec(v_dateDays_577_);
v___x_579_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_578_);
lean_dec(v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addDays___boxed(lean_object* v_date_580_, lean_object* v_days_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Time_PlainDate_addDays(v_date_580_, v_days_581_);
lean_dec(v_days_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays(lean_object* v_date_583_, lean_object* v_days_584_){
_start:
{
lean_object* v___x_585_; lean_object* v_dateDays_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_int_neg(v_days_584_);
v_dateDays_586_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_583_);
v___x_587_ = lean_int_add(v_dateDays_586_, v___x_585_);
lean_dec(v___x_585_);
lean_dec(v_dateDays_586_);
v___x_588_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_587_);
lean_dec(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subDays___boxed(lean_object* v_date_589_, lean_object* v_days_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Std_Time_PlainDate_subDays(v_date_589_, v_days_590_);
lean_dec(v_days_590_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks(lean_object* v_date_592_, lean_object* v_weeks_593_){
_start:
{
lean_object* v_dateDays_594_; lean_object* v___x_595_; lean_object* v_daysToAdd_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_dateDays_594_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_592_);
v___x_595_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_596_ = lean_int_mul(v_weeks_593_, v___x_595_);
v___x_597_ = lean_int_add(v_dateDays_594_, v_daysToAdd_596_);
lean_dec(v_daysToAdd_596_);
lean_dec(v_dateDays_594_);
v___x_598_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_597_);
lean_dec(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addWeeks___boxed(lean_object* v_date_599_, lean_object* v_weeks_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Time_PlainDate_addWeeks(v_date_599_, v_weeks_600_);
lean_dec(v_weeks_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks(lean_object* v_date_602_, lean_object* v_weeks_603_){
_start:
{
lean_object* v___x_604_; lean_object* v_dateDays_605_; lean_object* v___x_606_; lean_object* v_daysToAdd_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_604_ = lean_int_neg(v_weeks_603_);
v_dateDays_605_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_602_);
v___x_606_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v_daysToAdd_607_ = lean_int_mul(v___x_604_, v___x_606_);
lean_dec(v___x_604_);
v___x_608_ = lean_int_add(v_dateDays_605_, v_daysToAdd_607_);
lean_dec(v_daysToAdd_607_);
lean_dec(v_dateDays_605_);
v___x_609_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_608_);
lean_dec(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subWeeks___boxed(lean_object* v_date_610_, lean_object* v_weeks_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_Time_PlainDate_subWeeks(v_date_610_, v_weeks_611_);
lean_dec(v_weeks_611_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object* v_date_613_, lean_object* v_months_614_){
_start:
{
lean_object* v_year_615_; lean_object* v_month_616_; lean_object* v_day_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_650_; 
v_year_615_ = lean_ctor_get(v_date_613_, 0);
v_month_616_ = lean_ctor_get(v_date_613_, 1);
v_day_617_ = lean_ctor_get(v_date_613_, 2);
v_isSharedCheck_650_ = !lean_is_exclusive(v_date_613_);
if (v_isSharedCheck_650_ == 0)
{
v___x_619_ = v_date_613_;
v_isShared_620_ = v_isSharedCheck_650_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_day_617_);
lean_inc(v_month_616_);
lean_inc(v_year_615_);
lean_dec(v_date_613_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_650_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_totalMonths_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_wrappedMonths_626_; lean_object* v_yearsOffset_627_; lean_object* v___x_628_; uint8_t v___y_630_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_646_; 
v___x_621_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_622_ = lean_int_sub(v_month_616_, v___x_621_);
lean_dec(v_month_616_);
v_totalMonths_623_ = lean_int_add(v___x_622_, v_months_614_);
lean_dec(v___x_622_);
v___x_624_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_625_ = lean_int_emod(v_totalMonths_623_, v___x_624_);
v_wrappedMonths_626_ = lean_int_add(v___x_625_, v___x_621_);
lean_dec(v___x_625_);
v_yearsOffset_627_ = lean_int_ediv(v_totalMonths_623_, v___x_624_);
lean_dec(v_totalMonths_623_);
v___x_628_ = lean_int_add(v_year_615_, v_yearsOffset_627_);
lean_dec(v_yearsOffset_627_);
lean_dec(v_year_615_);
v___x_639_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_640_ = lean_int_mod(v___x_628_, v___x_639_);
v___x_641_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_646_ = lean_int_dec_eq(v___x_640_, v___x_641_);
lean_dec(v___x_640_);
if (v___x_646_ == 0)
{
v___y_630_ = v___x_646_;
goto v___jp_629_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_647_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_648_ = lean_int_mod(v___x_628_, v___x_647_);
v___x_649_ = lean_int_dec_eq(v___x_648_, v___x_641_);
lean_dec(v___x_648_);
if (v___x_649_ == 0)
{
if (v___x_646_ == 0)
{
goto v___jp_642_;
}
else
{
v___y_630_ = v___x_646_;
goto v___jp_629_;
}
}
else
{
goto v___jp_642_;
}
}
v___jp_629_:
{
lean_object* v_max_631_; uint8_t v___x_632_; 
v_max_631_ = l_Std_Time_Month_Ordinal_days(v___y_630_, v_wrappedMonths_626_);
v___x_632_ = lean_int_dec_lt(v_max_631_, v_day_617_);
if (v___x_632_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v_max_631_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v_wrappedMonths_626_);
lean_ctor_set(v___x_619_, 0, v___x_628_);
v___x_634_ = v___x_619_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_wrappedMonths_626_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_day_617_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
else
{
lean_object* v___x_637_; 
lean_dec(v_day_617_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 2, v_max_631_);
lean_ctor_set(v___x_619_, 1, v_wrappedMonths_626_);
lean_ctor_set(v___x_619_, 0, v___x_628_);
v___x_637_ = v___x_619_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_wrappedMonths_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_max_631_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
v___jp_642_:
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_644_ = lean_int_mod(v___x_628_, v___x_643_);
v___x_645_ = lean_int_dec_eq(v___x_644_, v___x_641_);
lean_dec(v___x_644_);
v___y_630_ = v___x_645_;
goto v___jp_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsClip___boxed(lean_object* v_date_651_, lean_object* v_months_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Std_Time_PlainDate_addMonthsClip(v_date_651_, v_months_652_);
lean_dec(v_months_652_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip(lean_object* v_date_654_, lean_object* v_months_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_int_neg(v_months_655_);
v___x_657_ = l_Std_Time_PlainDate_addMonthsClip(v_date_654_, v___x_656_);
lean_dec(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsClip___boxed(lean_object* v_date_658_, lean_object* v_months_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_Time_PlainDate_subMonthsClip(v_date_658_, v_months_659_);
lean_dec(v_months_659_);
return v_res_660_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__0(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_unsigned_to_nat(30u);
v___x_662_ = lean_nat_to_int(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__1(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__0, &l_Std_Time_PlainDate_rollOver___closed__0_once, _init_l_Std_Time_PlainDate_rollOver___closed__0);
v___x_664_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_665_ = lean_int_add(v___x_664_, v___x_663_);
return v___x_665_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__2(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_667_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__1, &l_Std_Time_PlainDate_rollOver___closed__1_once, _init_l_Std_Time_PlainDate_rollOver___closed__1);
v___x_668_ = lean_int_sub(v___x_667_, v___x_666_);
return v___x_668_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__3(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v_range_671_; 
v___x_669_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_670_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__2, &l_Std_Time_PlainDate_rollOver___closed__2_once, _init_l_Std_Time_PlainDate_rollOver___closed__2);
v_range_671_ = lean_int_add(v___x_670_, v___x_669_);
return v_range_671_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__4(void){
_start:
{
lean_object* v_range_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_range_672_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_673_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__5, &l_Std_Time_instInhabitedPlainDate___closed__5_once, _init_l_Std_Time_instInhabitedPlainDate___closed__5);
v___x_674_ = lean_int_emod(v___x_673_, v_range_672_);
return v___x_674_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__5(void){
_start:
{
lean_object* v_range_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_range_675_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_676_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__4, &l_Std_Time_PlainDate_rollOver___closed__4_once, _init_l_Std_Time_PlainDate_rollOver___closed__4);
v___x_677_ = lean_int_add(v___x_676_, v_range_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__6(void){
_start:
{
lean_object* v_range_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_range_678_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__3, &l_Std_Time_PlainDate_rollOver___closed__3_once, _init_l_Std_Time_PlainDate_rollOver___closed__3);
v___x_679_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__5, &l_Std_Time_PlainDate_rollOver___closed__5_once, _init_l_Std_Time_PlainDate_rollOver___closed__5);
v___x_680_ = lean_int_emod(v___x_679_, v_range_678_);
return v___x_680_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_rollOver___closed__7(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_682_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__6, &l_Std_Time_PlainDate_rollOver___closed__6_once, _init_l_Std_Time_PlainDate_rollOver___closed__6);
v___x_683_ = lean_int_add(v___x_682_, v___x_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver(lean_object* v_year_684_, lean_object* v_month_685_, lean_object* v_day_686_){
_start:
{
lean_object* v___y_688_; lean_object* v___x_694_; uint8_t v___y_696_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_708_; 
v___x_694_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_701_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_702_ = lean_int_mod(v_year_684_, v___x_701_);
v___x_703_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_708_ = lean_int_dec_eq(v___x_702_, v___x_703_);
lean_dec(v___x_702_);
if (v___x_708_ == 0)
{
v___y_696_ = v___x_708_;
goto v___jp_695_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_710_ = lean_int_mod(v_year_684_, v___x_709_);
v___x_711_ = lean_int_dec_eq(v___x_710_, v___x_703_);
lean_dec(v___x_710_);
if (v___x_711_ == 0)
{
if (v___x_708_ == 0)
{
goto v___jp_704_;
}
else
{
v___y_696_ = v___x_708_;
goto v___jp_695_;
}
}
else
{
goto v___jp_704_;
}
}
v___jp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_dateDays_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_690_ = lean_int_sub(v_day_686_, v___x_689_);
v_dateDays_691_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v___y_688_);
v___x_692_ = lean_int_add(v_dateDays_691_, v___x_690_);
lean_dec(v___x_690_);
lean_dec(v_dateDays_691_);
v___x_693_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_692_);
lean_dec(v___x_692_);
return v___x_693_;
}
v___jp_695_:
{
lean_object* v_max_697_; uint8_t v___x_698_; 
v_max_697_ = l_Std_Time_Month_Ordinal_days(v___y_696_, v_month_685_);
v___x_698_ = lean_int_dec_lt(v_max_697_, v___x_694_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; 
lean_dec(v_max_697_);
v___x_699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_699_, 0, v_year_684_);
lean_ctor_set(v___x_699_, 1, v_month_685_);
lean_ctor_set(v___x_699_, 2, v___x_694_);
v___y_688_ = v___x_699_;
goto v___jp_687_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_700_, 0, v_year_684_);
lean_ctor_set(v___x_700_, 1, v_month_685_);
lean_ctor_set(v___x_700_, 2, v_max_697_);
v___y_688_ = v___x_700_;
goto v___jp_687_;
}
}
v___jp_704_:
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_706_ = lean_int_mod(v_year_684_, v___x_705_);
v___x_707_ = lean_int_dec_eq(v___x_706_, v___x_703_);
lean_dec(v___x_706_);
v___y_696_ = v___x_707_;
goto v___jp_695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_rollOver___boxed(lean_object* v_year_712_, lean_object* v_month_713_, lean_object* v_day_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Std_Time_PlainDate_rollOver(v_year_712_, v_month_713_, v_day_714_);
lean_dec(v_day_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearClip(lean_object* v_dt_716_, lean_object* v_year_717_){
_start:
{
lean_object* v_month_718_; lean_object* v_day_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_744_; 
v_month_718_ = lean_ctor_get(v_dt_716_, 1);
v_day_719_ = lean_ctor_get(v_dt_716_, 2);
v_isSharedCheck_744_ = !lean_is_exclusive(v_dt_716_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v_dt_716_, 0);
lean_dec(v_unused_745_);
v___x_721_ = v_dt_716_;
v_isShared_722_ = v_isSharedCheck_744_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_day_719_);
lean_inc(v_month_718_);
lean_dec(v_dt_716_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_744_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
uint8_t v___y_724_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_740_; 
v___x_733_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_734_ = lean_int_mod(v_year_717_, v___x_733_);
v___x_735_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_740_ = lean_int_dec_eq(v___x_734_, v___x_735_);
lean_dec(v___x_734_);
if (v___x_740_ == 0)
{
v___y_724_ = v___x_740_;
goto v___jp_723_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_741_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_742_ = lean_int_mod(v_year_717_, v___x_741_);
v___x_743_ = lean_int_dec_eq(v___x_742_, v___x_735_);
lean_dec(v___x_742_);
if (v___x_743_ == 0)
{
if (v___x_740_ == 0)
{
goto v___jp_736_;
}
else
{
v___y_724_ = v___x_740_;
goto v___jp_723_;
}
}
else
{
goto v___jp_736_;
}
}
v___jp_723_:
{
lean_object* v_max_725_; uint8_t v___x_726_; 
v_max_725_ = l_Std_Time_Month_Ordinal_days(v___y_724_, v_month_718_);
v___x_726_ = lean_int_dec_lt(v_max_725_, v_day_719_);
if (v___x_726_ == 0)
{
lean_object* v___x_728_; 
lean_dec(v_max_725_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_year_717_);
v___x_728_ = v___x_721_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_year_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_month_718_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_day_719_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v___x_731_; 
lean_dec(v_day_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 2, v_max_725_);
lean_ctor_set(v___x_721_, 0, v_year_717_);
v___x_731_ = v___x_721_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_year_717_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_month_718_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_max_725_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
v___jp_736_:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_738_ = lean_int_mod(v_year_717_, v___x_737_);
v___x_739_ = lean_int_dec_eq(v___x_738_, v___x_735_);
lean_dec(v___x_738_);
v___y_724_ = v___x_739_;
goto v___jp_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withYearRollOver(lean_object* v_dt_746_, lean_object* v_year_747_){
_start:
{
lean_object* v_month_748_; lean_object* v_day_749_; lean_object* v___x_750_; 
v_month_748_ = lean_ctor_get(v_dt_746_, 1);
lean_inc(v_month_748_);
v_day_749_ = lean_ctor_get(v_dt_746_, 2);
lean_inc(v_day_749_);
lean_dec_ref(v_dt_746_);
v___x_750_ = l_Std_Time_PlainDate_rollOver(v_year_747_, v_month_748_, v_day_749_);
lean_dec(v_day_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object* v_date_751_, lean_object* v_months_752_){
_start:
{
lean_object* v_year_753_; lean_object* v_month_754_; lean_object* v_day_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_789_; 
v_year_753_ = lean_ctor_get(v_date_751_, 0);
v_month_754_ = lean_ctor_get(v_date_751_, 1);
v_day_755_ = lean_ctor_get(v_date_751_, 2);
v_isSharedCheck_789_ = !lean_is_exclusive(v_date_751_);
if (v_isSharedCheck_789_ == 0)
{
v___x_757_ = v_date_751_;
v_isShared_758_ = v_isSharedCheck_789_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_day_755_);
lean_inc(v_month_754_);
lean_inc(v_year_753_);
lean_dec(v_date_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_789_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___y_760_; lean_object* v___x_767_; uint8_t v___y_769_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_785_; 
v___x_767_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_778_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_779_ = lean_int_mod(v_year_753_, v___x_778_);
v___x_780_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_785_ = lean_int_dec_eq(v___x_779_, v___x_780_);
lean_dec(v___x_779_);
if (v___x_785_ == 0)
{
v___y_769_ = v___x_785_;
goto v___jp_768_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_787_ = lean_int_mod(v_year_753_, v___x_786_);
v___x_788_ = lean_int_dec_eq(v___x_787_, v___x_780_);
lean_dec(v___x_787_);
if (v___x_788_ == 0)
{
if (v___x_785_ == 0)
{
goto v___jp_781_;
}
else
{
v___y_769_ = v___x_785_;
goto v___jp_768_;
}
}
else
{
goto v___jp_781_;
}
}
v___jp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_dateDays_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_761_ = l_Std_Time_PlainDate_addMonthsClip(v___y_760_, v_months_752_);
v___x_762_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_763_ = lean_int_sub(v_day_755_, v___x_762_);
lean_dec(v_day_755_);
v_dateDays_764_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v___x_761_);
v___x_765_ = lean_int_add(v_dateDays_764_, v___x_763_);
lean_dec(v___x_763_);
lean_dec(v_dateDays_764_);
v___x_766_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_765_);
lean_dec(v___x_765_);
return v___x_766_;
}
v___jp_768_:
{
lean_object* v_max_770_; uint8_t v___x_771_; 
v_max_770_ = l_Std_Time_Month_Ordinal_days(v___y_769_, v_month_754_);
v___x_771_ = lean_int_dec_lt(v_max_770_, v___x_767_);
if (v___x_771_ == 0)
{
lean_object* v___x_773_; 
lean_dec(v_max_770_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 2, v___x_767_);
v___x_773_ = v___x_757_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_year_753_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_month_754_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v___x_767_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
v___y_760_ = v___x_773_;
goto v___jp_759_;
}
}
else
{
lean_object* v___x_776_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 2, v_max_770_);
v___x_776_ = v___x_757_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_year_753_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_month_754_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_max_770_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
v___y_760_ = v___x_776_;
goto v___jp_759_;
}
}
}
v___jp_781_:
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_782_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_783_ = lean_int_mod(v_year_753_, v___x_782_);
v___x_784_ = lean_int_dec_eq(v___x_783_, v___x_780_);
lean_dec(v___x_783_);
v___y_769_ = v___x_784_;
goto v___jp_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addMonthsRollOver___boxed(lean_object* v_date_790_, lean_object* v_months_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_790_, v_months_791_);
lean_dec(v_months_791_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver(lean_object* v_date_793_, lean_object* v_months_794_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_int_neg(v_months_794_);
v___x_796_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_793_, v___x_795_);
lean_dec(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subMonthsRollOver___boxed(lean_object* v_date_797_, lean_object* v_months_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_Time_PlainDate_subMonthsRollOver(v_date_797_, v_months_798_);
lean_dec(v_months_798_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver(lean_object* v_date_800_, lean_object* v_years_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_803_ = lean_int_mul(v_years_801_, v___x_802_);
v___x_804_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_800_, v___x_803_);
lean_dec(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsRollOver___boxed(lean_object* v_date_805_, lean_object* v_years_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_Time_PlainDate_addYearsRollOver(v_date_805_, v_years_806_);
lean_dec(v_years_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver(lean_object* v_date_808_, lean_object* v_years_809_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_810_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_811_ = lean_int_mul(v_years_809_, v___x_810_);
v___x_812_ = lean_int_neg(v___x_811_);
lean_dec(v___x_811_);
v___x_813_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_808_, v___x_812_);
lean_dec(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsRollOver___boxed(lean_object* v_date_814_, lean_object* v_years_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_Time_PlainDate_subYearsRollOver(v_date_814_, v_years_815_);
lean_dec(v_years_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip(lean_object* v_date_817_, lean_object* v_years_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_820_ = lean_int_mul(v_years_818_, v___x_819_);
v___x_821_ = l_Std_Time_PlainDate_addMonthsClip(v_date_817_, v___x_820_);
lean_dec(v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_addYearsClip___boxed(lean_object* v_date_822_, lean_object* v_years_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_Time_PlainDate_addYearsClip(v_date_822_, v_years_823_);
lean_dec(v_years_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip(lean_object* v_date_825_, lean_object* v_years_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_827_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__2);
v___x_828_ = lean_int_mul(v_years_826_, v___x_827_);
v___x_829_ = lean_int_neg(v___x_828_);
lean_dec(v___x_828_);
v___x_830_ = l_Std_Time_PlainDate_addMonthsClip(v_date_825_, v___x_829_);
lean_dec(v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_subYearsClip___boxed(lean_object* v_date_831_, lean_object* v_years_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_Time_PlainDate_subYearsClip(v_date_831_, v_years_832_);
lean_dec(v_years_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysClip(lean_object* v_dt_834_, lean_object* v_days_835_){
_start:
{
lean_object* v_year_836_; lean_object* v_month_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_862_; 
v_year_836_ = lean_ctor_get(v_dt_834_, 0);
v_month_837_ = lean_ctor_get(v_dt_834_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_dt_834_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v_dt_834_, 2);
lean_dec(v_unused_863_);
v___x_839_ = v_dt_834_;
v_isShared_840_ = v_isSharedCheck_862_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_month_837_);
lean_inc(v_year_836_);
lean_dec(v_dt_834_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_862_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___y_842_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_858_; 
v___x_851_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_852_ = lean_int_mod(v_year_836_, v___x_851_);
v___x_853_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_858_ = lean_int_dec_eq(v___x_852_, v___x_853_);
lean_dec(v___x_852_);
if (v___x_858_ == 0)
{
v___y_842_ = v___x_858_;
goto v___jp_841_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_860_ = lean_int_mod(v_year_836_, v___x_859_);
v___x_861_ = lean_int_dec_eq(v___x_860_, v___x_853_);
lean_dec(v___x_860_);
if (v___x_861_ == 0)
{
if (v___x_858_ == 0)
{
goto v___jp_854_;
}
else
{
v___y_842_ = v___x_858_;
goto v___jp_841_;
}
}
else
{
goto v___jp_854_;
}
}
v___jp_841_:
{
lean_object* v_max_843_; uint8_t v___x_844_; 
v_max_843_ = l_Std_Time_Month_Ordinal_days(v___y_842_, v_month_837_);
v___x_844_ = lean_int_dec_lt(v_max_843_, v_days_835_);
if (v___x_844_ == 0)
{
lean_object* v___x_846_; 
lean_dec(v_max_843_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 2, v_days_835_);
v___x_846_ = v___x_839_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_year_836_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_month_837_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_days_835_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v___x_849_; 
lean_dec(v_days_835_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 2, v_max_843_);
v___x_849_ = v___x_839_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_year_836_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_month_837_);
lean_ctor_set(v_reuseFailAlloc_850_, 2, v_max_843_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
v___jp_854_:
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_855_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_856_ = lean_int_mod(v_year_836_, v___x_855_);
v___x_857_ = lean_int_dec_eq(v___x_856_, v___x_853_);
lean_dec(v___x_856_);
v___y_842_ = v___x_857_;
goto v___jp_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver(lean_object* v_dt_864_, lean_object* v_days_865_){
_start:
{
lean_object* v_year_866_; lean_object* v_month_867_; lean_object* v___x_868_; 
v_year_866_ = lean_ctor_get(v_dt_864_, 0);
lean_inc(v_year_866_);
v_month_867_ = lean_ctor_get(v_dt_864_, 1);
lean_inc(v_month_867_);
lean_dec_ref(v_dt_864_);
v___x_868_ = l_Std_Time_PlainDate_rollOver(v_year_866_, v_month_867_, v_days_865_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withDaysRollOver___boxed(lean_object* v_dt_869_, lean_object* v_days_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_Time_PlainDate_withDaysRollOver(v_dt_869_, v_days_870_);
lean_dec(v_days_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthClip(lean_object* v_dt_872_, lean_object* v_month_873_){
_start:
{
lean_object* v_year_874_; lean_object* v_day_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_900_; 
v_year_874_ = lean_ctor_get(v_dt_872_, 0);
v_day_875_ = lean_ctor_get(v_dt_872_, 2);
v_isSharedCheck_900_ = !lean_is_exclusive(v_dt_872_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v_dt_872_, 1);
lean_dec(v_unused_901_);
v___x_877_ = v_dt_872_;
v_isShared_878_ = v_isSharedCheck_900_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_day_875_);
lean_inc(v_year_874_);
lean_dec(v_dt_872_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_900_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v___y_880_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_896_; 
v___x_889_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_890_ = lean_int_mod(v_year_874_, v___x_889_);
v___x_891_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_896_ = lean_int_dec_eq(v___x_890_, v___x_891_);
lean_dec(v___x_890_);
if (v___x_896_ == 0)
{
v___y_880_ = v___x_896_;
goto v___jp_879_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_897_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_898_ = lean_int_mod(v_year_874_, v___x_897_);
v___x_899_ = lean_int_dec_eq(v___x_898_, v___x_891_);
lean_dec(v___x_898_);
if (v___x_899_ == 0)
{
if (v___x_896_ == 0)
{
goto v___jp_892_;
}
else
{
v___y_880_ = v___x_896_;
goto v___jp_879_;
}
}
else
{
goto v___jp_892_;
}
}
v___jp_879_:
{
lean_object* v_max_881_; uint8_t v___x_882_; 
v_max_881_ = l_Std_Time_Month_Ordinal_days(v___y_880_, v_month_873_);
v___x_882_ = lean_int_dec_lt(v_max_881_, v_day_875_);
if (v___x_882_ == 0)
{
lean_object* v___x_884_; 
lean_dec(v_max_881_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v_month_873_);
v___x_884_ = v___x_877_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_year_874_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_month_873_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_day_875_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec(v_day_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 2, v_max_881_);
lean_ctor_set(v___x_877_, 1, v_month_873_);
v___x_887_ = v___x_877_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_year_874_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_month_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_max_881_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
v___jp_892_:
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_894_ = lean_int_mod(v_year_874_, v___x_893_);
v___x_895_ = lean_int_dec_eq(v___x_894_, v___x_891_);
lean_dec(v___x_894_);
v___y_880_ = v___x_895_;
goto v___jp_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withMonthRollOver(lean_object* v_dt_902_, lean_object* v_month_903_){
_start:
{
lean_object* v_year_904_; lean_object* v_day_905_; lean_object* v___x_906_; 
v_year_904_ = lean_ctor_get(v_dt_902_, 0);
lean_inc(v_year_904_);
v_day_905_ = lean_ctor_get(v_dt_902_, 2);
lean_inc(v_day_905_);
lean_dec_ref(v_dt_902_);
v___x_906_ = l_Std_Time_PlainDate_rollOver(v_year_904_, v_month_903_, v_day_905_);
lean_dec(v_day_905_);
return v___x_906_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__0(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_908_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_909_ = lean_int_sub(v___x_908_, v___x_907_);
return v___x_909_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__1(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_range_912_; 
v___x_910_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_911_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__0, &l_Std_Time_PlainDate_weekday___closed__0_once, _init_l_Std_Time_PlainDate_weekday___closed__0);
v_range_912_ = lean_int_add(v___x_911_, v___x_910_);
return v_range_912_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__2(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_914_ = lean_int_neg(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_weekday___closed__3(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_unsigned_to_nat(6u);
v___x_916_ = lean_nat_to_int(v___x_915_);
return v___x_916_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_PlainDate_weekday(lean_object* v_date_917_){
_start:
{
lean_object* v___y_919_; lean_object* v_days_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_days_928_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_917_);
v___x_929_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_930_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__2, &l_Std_Time_PlainDate_weekday___closed__2_once, _init_l_Std_Time_PlainDate_weekday___closed__2);
v___x_931_ = lean_int_dec_le(v___x_930_, v_days_928_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_932_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__8);
v___x_933_ = lean_int_add(v_days_928_, v___x_932_);
lean_dec(v_days_928_);
v___x_934_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_935_ = lean_int_emod(v___x_933_, v___x_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__3, &l_Std_Time_PlainDate_weekday___closed__3_once, _init_l_Std_Time_PlainDate_weekday___closed__3);
v___x_937_ = lean_int_add(v___x_935_, v___x_936_);
lean_dec(v___x_935_);
v___y_919_ = v___x_937_;
goto v___jp_918_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_int_add(v_days_928_, v___x_929_);
lean_dec(v_days_928_);
v___x_939_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_940_ = lean_int_emod(v___x_938_, v___x_939_);
lean_dec(v___x_938_);
v___y_919_ = v___x_940_;
goto v___jp_918_;
}
v___jp_918_:
{
lean_object* v___x_920_; lean_object* v_range_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_920_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v_range_921_ = lean_obj_once(&l_Std_Time_PlainDate_weekday___closed__1, &l_Std_Time_PlainDate_weekday___closed__1_once, _init_l_Std_Time_PlainDate_weekday___closed__1);
v___x_922_ = lean_int_sub(v___y_919_, v___x_920_);
lean_dec(v___y_919_);
v___x_923_ = lean_int_emod(v___x_922_, v_range_921_);
lean_dec(v___x_922_);
v___x_924_ = lean_int_add(v___x_923_, v_range_921_);
lean_dec(v___x_923_);
v___x_925_ = lean_int_emod(v___x_924_, v_range_921_);
lean_dec(v___x_924_);
v___x_926_ = lean_int_add(v___x_925_, v___x_920_);
lean_dec(v___x_925_);
v___x_927_ = l_Std_Time_Weekday_ofOrdinal(v___x_926_);
lean_dec(v___x_926_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekday___boxed(lean_object* v_date_941_){
_start:
{
uint8_t v_res_942_; lean_object* v_r_943_; 
v_res_942_ = l_Std_Time_PlainDate_weekday(v_date_941_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object* v_date_944_){
_start:
{
lean_object* v_year_945_; lean_object* v_month_946_; lean_object* v_day_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_985_; 
v_year_945_ = lean_ctor_get(v_date_944_, 0);
v_month_946_ = lean_ctor_get(v_date_944_, 1);
v_day_947_ = lean_ctor_get(v_date_944_, 2);
v_isSharedCheck_985_ = !lean_is_exclusive(v_date_944_);
if (v_isSharedCheck_985_ == 0)
{
v___x_949_ = v_date_944_;
v_isShared_950_ = v_isSharedCheck_985_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_day_947_);
lean_inc(v_month_946_);
lean_inc(v_year_945_);
lean_dec(v_date_944_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_985_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___y_954_; lean_object* v___x_963_; uint8_t v___y_965_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_981_; 
v___x_951_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_952_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_963_ = lean_obj_once(&l_Std_Time_PlainDate_rollOver___closed__7, &l_Std_Time_PlainDate_rollOver___closed__7_once, _init_l_Std_Time_PlainDate_rollOver___closed__7);
v___x_974_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0);
v___x_975_ = lean_int_mod(v_year_945_, v___x_974_);
v___x_976_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_981_ = lean_int_dec_eq(v___x_975_, v___x_976_);
lean_dec(v___x_975_);
if (v___x_981_ == 0)
{
v___y_965_ = v___x_981_;
goto v___jp_964_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_982_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2);
v___x_983_ = lean_int_mod(v_year_945_, v___x_982_);
v___x_984_ = lean_int_dec_eq(v___x_983_, v___x_976_);
lean_dec(v___x_983_);
if (v___x_984_ == 0)
{
if (v___x_981_ == 0)
{
goto v___jp_977_;
}
else
{
v___y_965_ = v___x_981_;
goto v___jp_964_;
}
}
else
{
goto v___jp_977_;
}
}
v___jp_953_:
{
uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_955_ = l_Std_Time_PlainDate_weekday(v___y_954_);
v___x_956_ = l_Std_Time_Weekday_toOrdinal(v___x_955_);
v___x_957_ = lean_obj_once(&l_Std_Time_PlainDate_weekOfMonth___closed__0, &l_Std_Time_PlainDate_weekOfMonth___closed__0_once, _init_l_Std_Time_PlainDate_weekOfMonth___closed__0);
v___x_958_ = lean_int_add(v___x_956_, v___x_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_int_add(v_day_947_, v___x_957_);
lean_dec(v_day_947_);
v___x_960_ = lean_int_add(v___x_959_, v___x_958_);
lean_dec(v___x_958_);
lean_dec(v___x_959_);
v___x_961_ = lean_int_ediv(v___x_960_, v___x_952_);
lean_dec(v___x_960_);
v___x_962_ = lean_int_add(v___x_961_, v___x_951_);
lean_dec(v___x_961_);
return v___x_962_;
}
v___jp_964_:
{
lean_object* v_max_966_; uint8_t v___x_967_; 
v_max_966_ = l_Std_Time_Month_Ordinal_days(v___y_965_, v_month_946_);
v___x_967_ = lean_int_dec_lt(v_max_966_, v___x_963_);
if (v___x_967_ == 0)
{
lean_object* v___x_969_; 
lean_dec(v_max_966_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v___x_963_);
v___x_969_ = v___x_949_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_year_945_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v_month_946_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v___x_963_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
v___y_954_ = v___x_969_;
goto v___jp_953_;
}
}
else
{
lean_object* v___x_972_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 2, v_max_966_);
v___x_972_ = v___x_949_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_year_945_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_month_946_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_max_966_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
v___y_954_ = v___x_972_;
goto v___jp_953_;
}
}
}
v___jp_977_:
{
lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_978_ = lean_obj_once(&l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1, &l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once, _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1);
v___x_979_ = lean_int_mod(v_year_945_, v___x_978_);
v___x_980_ = lean_int_dec_eq(v___x_979_, v___x_976_);
lean_dec(v___x_979_);
v___y_965_ = v___x_980_;
goto v___jp_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday(lean_object* v_date_986_, uint8_t v_desiredWeekday_987_){
_start:
{
lean_object* v___y_989_; uint8_t v___x_993_; lean_object* v_weekday_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
lean_inc_ref(v_date_986_);
v___x_993_ = l_Std_Time_PlainDate_weekday(v_date_986_);
v_weekday_994_ = l_Std_Time_Weekday_toOrdinal(v___x_993_);
v___x_995_ = l_Std_Time_Weekday_toOrdinal(v_desiredWeekday_987_);
v___x_996_ = lean_int_neg(v_weekday_994_);
lean_dec(v_weekday_994_);
v___x_997_ = lean_int_add(v___x_995_, v___x_996_);
lean_dec(v___x_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__25, &l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25);
v___x_999_ = lean_int_dec_lt(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
v___y_989_ = v___x_997_;
goto v___jp_988_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1001_ = lean_int_add(v___x_997_, v___x_1000_);
lean_dec(v___x_997_);
v___y_989_ = v___x_1001_;
goto v___jp_988_;
}
v___jp_988_:
{
lean_object* v_dateDays_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_dateDays_990_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_986_);
v___x_991_ = lean_int_add(v_dateDays_990_, v___y_989_);
lean_dec(v___y_989_);
lean_dec(v_dateDays_990_);
v___x_992_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_991_);
lean_dec(v___x_991_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_withWeekday___boxed(lean_object* v_date_1002_, lean_object* v_desiredWeekday_1003_){
_start:
{
uint8_t v_desiredWeekday_boxed_1004_; lean_object* v_res_1005_; 
v_desiredWeekday_boxed_1004_ = lean_unbox(v_desiredWeekday_1003_);
v_res_1005_ = l_Std_Time_PlainDate_withWeekday(v_date_1002_, v_desiredWeekday_boxed_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object* v_date_1006_){
_start:
{
lean_object* v_year_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_w_1017_; uint8_t v___x_1018_; 
v_year_1007_ = lean_ctor_get(v_date_1006_, 0);
lean_inc(v_year_1007_);
v___x_1008_ = lean_obj_once(&l_Std_Time_instInhabitedPlainDate___closed__0, &l_Std_Time_instInhabitedPlainDate___closed__0_once, _init_l_Std_Time_instInhabitedPlainDate___closed__0);
v___x_1009_ = lean_obj_once(&l_Std_Time_instReprPlainDate_repr___redArg___closed__8, &l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once, _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8);
v___x_1010_ = lean_obj_once(&l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11, &l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11_once, _init_l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch___closed__11);
v___x_1011_ = l_Std_Time_PlainDate_dayOfYear(v_date_1006_);
v___x_1012_ = lean_int_add(v___x_1010_, v___x_1011_);
lean_dec(v___x_1011_);
v___x_1013_ = l_Std_Time_PlainDate_weekday(v_date_1006_);
v___x_1014_ = l_Std_Time_Weekday_toOrdinal(v___x_1013_);
v___x_1015_ = lean_int_neg(v___x_1014_);
lean_dec(v___x_1014_);
v___x_1016_ = lean_int_add(v___x_1012_, v___x_1015_);
lean_dec(v___x_1015_);
lean_dec(v___x_1012_);
v_w_1017_ = lean_int_ediv(v___x_1016_, v___x_1009_);
lean_dec(v___x_1016_);
v___x_1018_ = lean_int_dec_lt(v_w_1017_, v___x_1008_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = l_Std_Time_Year_Offset_weeks(v_year_1007_);
lean_dec(v_year_1007_);
v___x_1020_ = lean_int_dec_lt(v___x_1019_, v_w_1017_);
lean_dec(v___x_1019_);
if (v___x_1020_ == 0)
{
return v_w_1017_;
}
else
{
lean_dec(v_w_1017_);
return v___x_1008_;
}
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v_w_1017_);
v___x_1021_ = lean_int_sub(v_year_1007_, v___x_1008_);
lean_dec(v_year_1007_);
v___x_1022_ = l_Std_Time_Year_Offset_weeks(v___x_1021_);
lean_dec(v___x_1021_);
return v___x_1022_;
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
l_Std_Time_instOrdPlainDate = _init_l_Std_Time_instOrdPlainDate();
lean_mark_persistent(l_Std_Time_instOrdPlainDate);
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
