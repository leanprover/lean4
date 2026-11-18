// Lean compiler output
// Module: Std.Time.Time.PlainTime
// Imports: public import Std.Time.Time.Basic
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
lean_object* l_Std_Time_Second_instOfNatOrdinal(uint8_t, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_Hour_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Time_Minute_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* l_Std_Time_Nanosecond_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Std_Time_Second_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Minute_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Hour_instOrdOrdinal___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprPlainTime_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hour"};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_instReprPlainTime_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "minute"};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Time_instReprPlainTime_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__12;
static const lean_string_object l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "second"};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__14 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__14_value;
static const lean_string_object l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "nanosecond"};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__16_value;
static lean_once_cell_t l_Std_Time_instReprPlainTime_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__17;
static const lean_string_object l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__18 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value;
static lean_once_cell_t l_Std_Time_instReprPlainTime_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__19;
static lean_once_cell_t l_Std_Time_instReprPlainTime_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__20;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__21 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__21_value;
static const lean_ctor_object l_Std_Time_instReprPlainTime_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__18_value)}};
static const lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__22 = (const lean_object*)&l_Std_Time_instReprPlainTime_repr___redArg___closed__22_value;
static lean_once_cell_t l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprPlainTime_repr___redArg___closed__23;
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainTime_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainTime_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainTime_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainTime_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprPlainTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprPlainTime_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprPlainTime___closed__0 = (const lean_object*)&l_Std_Time_instReprPlainTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprPlainTime = (const lean_object*)&l_Std_Time_instReprPlainTime___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainTime_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainTime_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainTime___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__0;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__1;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__2;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__3;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__4;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__5;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__6;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__7;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__8;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__9;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__10;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__11;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__12;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__13;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__14;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__15;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__16;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__17;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__18;
static lean_once_cell_t l_Std_Time_instInhabitedPlainTime___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedPlainTime___closed__19;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedPlainTime;
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__3___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainTime___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__0 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__0_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainTime___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__1 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__1_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainTime___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__2 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__2_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdPlainTime___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__3 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__3_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Hour_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__4 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__4_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Minute_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__5 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__5_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Nanosecond_instOrdOrdinal___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__6 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__6_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__4_value),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__0_value)} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__7 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__7_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__5_value),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__1_value)} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__8 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__8_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Second_instOrdOrdinal___aux__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__9 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__9_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__9_value),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__2_value)} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__10 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__10_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__6_value),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__3_value)} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__11 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__11_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareLex___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__10_value),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__11_value)} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__12 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__12_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareLex___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__8_value),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__12_value)} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__13 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__13_value;
static const lean_closure_object l_Std_Time_instOrdPlainTime___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareLex___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__7_value),((lean_object*)&l_Std_Time_instOrdPlainTime___closed__13_value)} };
static const lean_object* l_Std_Time_instOrdPlainTime___closed__14 = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__14_value;
LEAN_EXPORT const lean_object* l_Std_Time_instOrdPlainTime = (const lean_object*)&l_Std_Time_instOrdPlainTime___closed__14_value;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__0;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__1;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__2;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__3;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__4;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__5;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__6;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__7;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__8;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__9;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__10;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__11;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__12;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__13;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__14;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__15;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__16;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_midnight;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSecondsNano(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__1(lean_object*);
static lean_once_cell_t l_Std_Time_PlainTime_toMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toMilliseconds___closed__0;
static lean_once_cell_t l_Std_Time_PlainTime_toMilliseconds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toMilliseconds___closed__1;
static lean_once_cell_t l_Std_Time_PlainTime_toMilliseconds___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toMilliseconds___closed__2;
static lean_once_cell_t l_Std_Time_PlainTime_toMilliseconds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toMilliseconds___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_PlainTime_toNanoseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toNanoseconds___closed__0;
static lean_once_cell_t l_Std_Time_PlainTime_toNanoseconds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toNanoseconds___closed__1;
static lean_once_cell_t l_Std_Time_PlainTime_toNanoseconds___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toNanoseconds___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_PlainTime_toSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toSeconds___closed__0;
static lean_once_cell_t l_Std_Time_PlainTime_toSeconds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toSeconds___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toHours___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_PlainTime_ofNanoseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_ofNanoseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMinutes___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond___boxed(lean_object*);
static const lean_closure_object l_Std_Time_PlainTime_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_addNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHAddOffset = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_subNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHSubOffset = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_addMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHAddOffset__1___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHAddOffset__1 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_subMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHSubOffset__1___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHSubOffset__1 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_addSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHAddOffset__2___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHAddOffset__2 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_subSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHSubOffset__2___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHSubOffset__2 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_addMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHAddOffset__3___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHAddOffset__3 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_subMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHSubOffset__3___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHSubOffset__3 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_addHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHAddOffset__4___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHAddOffset__4 = (const lean_object*)&l_Std_Time_PlainTime_instHAddOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_subHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instHSubOffset__4___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instHSubOffset__4 = (const lean_object*)&l_Std_Time_PlainTime_instHSubOffset__4___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprPlainTime_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(8u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_unsigned_to_nat(10u);
v___x_25_ = lean_nat_to_int(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(14u);
v___x_33_ = lean_nat_to_int(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__0));
v___x_36_ = lean_string_length(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__19, &l_Std_Time_instReprPlainTime_repr___redArg___closed__19_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__19);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainTime_repr___redArg(lean_object* v_x_45_){
_start:
{
lean_object* v_hour_46_; lean_object* v_minute_47_; lean_object* v_second_48_; lean_object* v_nanosecond_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___y_77_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_hour_46_ = lean_ctor_get(v_x_45_, 0);
v_minute_47_ = lean_ctor_get(v_x_45_, 1);
v_second_48_ = lean_ctor_get(v_x_45_, 2);
v_nanosecond_49_ = lean_ctor_get(v_x_45_, 3);
v___x_50_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__5));
v___x_51_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__6));
v___x_52_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__7, &l_Std_Time_instReprPlainTime_repr___redArg___closed__7_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__7);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = l_Std_Time_Hour_instReprOrdinal___lam__0(v_hour_46_, v___x_53_);
v___x_55_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_52_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = 0;
v___x_57_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*1, v___x_56_);
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_51_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__9));
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = lean_box(1);
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__11));
v___x_64_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_50_);
v___x_66_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__12, &l_Std_Time_instReprPlainTime_repr___redArg___closed__12_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__12);
v___x_67_ = l_Std_Time_Minute_instReprOrdinal___lam__0(v_minute_47_, v___x_53_);
v___x_68_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_56_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_65_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_59_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_61_);
v___x_73_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__14));
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_50_);
v___x_98_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_99_ = lean_int_dec_lt(v_second_48_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = l_Int_repr(v_second_48_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___y_77_ = v___x_101_;
goto v___jp_76_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = l_Int_repr(v_second_48_);
v___x_103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
v___x_104_ = l_Repr_addAppParen(v___x_103_, v___x_53_);
v___y_77_ = v___x_104_;
goto v___jp_76_;
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_78_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_66_);
lean_ctor_set(v___x_78_, 1, v___y_77_);
v___x_79_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*1, v___x_56_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_75_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_59_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_61_);
v___x_83_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__16));
v___x_84_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_50_);
v___x_86_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__17, &l_Std_Time_instReprPlainTime_repr___redArg___closed__17_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__17);
v___x_87_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanosecond_49_, v___x_53_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_56_);
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_85_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__20, &l_Std_Time_instReprPlainTime_repr___redArg___closed__20_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__20);
v___x_92_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__21));
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_90_);
v___x_94_ = ((lean_object*)(l_Std_Time_instReprPlainTime_repr___redArg___closed__22));
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_56_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainTime_repr___redArg___boxed(lean_object* v_x_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Std_Time_instReprPlainTime_repr___redArg(v_x_105_);
lean_dec_ref(v_x_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainTime_repr(lean_object* v_x_107_, lean_object* v_prec_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Std_Time_instReprPlainTime_repr___redArg(v_x_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprPlainTime_repr___boxed(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_Time_instReprPlainTime_repr(v_x_110_, v_prec_111_);
lean_dec(v_prec_111_);
lean_dec_ref(v_x_110_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainTime_decEq(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_hour_117_; lean_object* v_minute_118_; lean_object* v_second_119_; lean_object* v_nanosecond_120_; lean_object* v_hour_121_; lean_object* v_minute_122_; lean_object* v_second_123_; lean_object* v_nanosecond_124_; uint8_t v___x_125_; 
v_hour_117_ = lean_ctor_get(v_x_115_, 0);
v_minute_118_ = lean_ctor_get(v_x_115_, 1);
v_second_119_ = lean_ctor_get(v_x_115_, 2);
v_nanosecond_120_ = lean_ctor_get(v_x_115_, 3);
v_hour_121_ = lean_ctor_get(v_x_116_, 0);
v_minute_122_ = lean_ctor_get(v_x_116_, 1);
v_second_123_ = lean_ctor_get(v_x_116_, 2);
v_nanosecond_124_ = lean_ctor_get(v_x_116_, 3);
v___x_125_ = lean_int_dec_eq(v_hour_117_, v_hour_121_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = lean_int_dec_eq(v_minute_118_, v_minute_122_);
if (v___x_126_ == 0)
{
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_int_dec_eq(v_second_119_, v_second_123_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
v___x_128_ = lean_int_dec_eq(v_nanosecond_120_, v_nanosecond_124_);
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainTime_decEq___boxed(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_129_, v_x_130_);
lean_dec_ref(v_x_130_);
lean_dec_ref(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqPlainTime(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_133_, v_x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainTime___boxed(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Std_Time_instDecidableEqPlainTime(v_x_136_, v_x_137_);
lean_dec_ref(v_x_137_);
lean_dec_ref(v_x_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__0(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(23u);
v___x_141_ = lean_nat_to_int(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__0, &l_Std_Time_instInhabitedPlainTime___closed__0_once, _init_l_Std_Time_instInhabitedPlainTime___closed__0);
v___x_143_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_144_ = lean_int_add(v___x_143_, v___x_142_);
return v___x_144_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__2(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_146_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__1, &l_Std_Time_instInhabitedPlainTime___closed__1_once, _init_l_Std_Time_instInhabitedPlainTime___closed__1);
v___x_147_ = lean_int_sub(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__3(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__4(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_range_152_; 
v___x_150_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_151_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__2, &l_Std_Time_instInhabitedPlainTime___closed__2_once, _init_l_Std_Time_instInhabitedPlainTime___closed__2);
v_range_152_ = lean_int_add(v___x_151_, v___x_150_);
return v_range_152_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__5(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_154_ = lean_int_sub(v___x_153_, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__6(void){
_start:
{
lean_object* v_range_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_range_155_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__4, &l_Std_Time_instInhabitedPlainTime___closed__4_once, _init_l_Std_Time_instInhabitedPlainTime___closed__4);
v___x_156_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_157_ = lean_int_emod(v___x_156_, v_range_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__7(void){
_start:
{
lean_object* v_range_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_range_158_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__4, &l_Std_Time_instInhabitedPlainTime___closed__4_once, _init_l_Std_Time_instInhabitedPlainTime___closed__4);
v___x_159_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__6, &l_Std_Time_instInhabitedPlainTime___closed__6_once, _init_l_Std_Time_instInhabitedPlainTime___closed__6);
v___x_160_ = lean_int_add(v___x_159_, v_range_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__8(void){
_start:
{
lean_object* v_range_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_range_161_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__4, &l_Std_Time_instInhabitedPlainTime___closed__4_once, _init_l_Std_Time_instInhabitedPlainTime___closed__4);
v___x_162_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__7, &l_Std_Time_instInhabitedPlainTime___closed__7_once, _init_l_Std_Time_instInhabitedPlainTime___closed__7);
v___x_163_ = lean_int_emod(v___x_162_, v_range_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__9(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_165_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__8, &l_Std_Time_instInhabitedPlainTime___closed__8_once, _init_l_Std_Time_instInhabitedPlainTime___closed__8);
v___x_166_ = lean_int_add(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__10(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(59u);
v___x_168_ = lean_nat_to_int(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__11(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__10, &l_Std_Time_instInhabitedPlainTime___closed__10_once, _init_l_Std_Time_instInhabitedPlainTime___closed__10);
v___x_170_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_171_ = lean_int_add(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__12(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_173_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__11, &l_Std_Time_instInhabitedPlainTime___closed__11_once, _init_l_Std_Time_instInhabitedPlainTime___closed__11);
v___x_174_ = lean_int_sub(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__13(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_range_177_; 
v___x_175_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_176_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__12, &l_Std_Time_instInhabitedPlainTime___closed__12_once, _init_l_Std_Time_instInhabitedPlainTime___closed__12);
v_range_177_ = lean_int_add(v___x_176_, v___x_175_);
return v_range_177_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__14(void){
_start:
{
lean_object* v_range_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_range_178_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__13, &l_Std_Time_instInhabitedPlainTime___closed__13_once, _init_l_Std_Time_instInhabitedPlainTime___closed__13);
v___x_179_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_180_ = lean_int_emod(v___x_179_, v_range_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__15(void){
_start:
{
lean_object* v_range_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_range_181_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__13, &l_Std_Time_instInhabitedPlainTime___closed__13_once, _init_l_Std_Time_instInhabitedPlainTime___closed__13);
v___x_182_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__14, &l_Std_Time_instInhabitedPlainTime___closed__14_once, _init_l_Std_Time_instInhabitedPlainTime___closed__14);
v___x_183_ = lean_int_add(v___x_182_, v_range_181_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__16(void){
_start:
{
lean_object* v_range_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_range_184_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__13, &l_Std_Time_instInhabitedPlainTime___closed__13_once, _init_l_Std_Time_instInhabitedPlainTime___closed__13);
v___x_185_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__15, &l_Std_Time_instInhabitedPlainTime___closed__15_once, _init_l_Std_Time_instInhabitedPlainTime___closed__15);
v___x_186_ = lean_int_emod(v___x_185_, v_range_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__17(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_188_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__16, &l_Std_Time_instInhabitedPlainTime___closed__16_once, _init_l_Std_Time_instInhabitedPlainTime___closed__16);
v___x_189_ = lean_int_add(v___x_188_, v___x_187_);
return v___x_189_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__18(void){
_start:
{
lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = 1;
v___x_192_ = l_Std_Time_Second_instOfNatOrdinal(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__19(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_193_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_194_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__18, &l_Std_Time_instInhabitedPlainTime___closed__18_once, _init_l_Std_Time_instInhabitedPlainTime___closed__18);
v___x_195_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__17, &l_Std_Time_instInhabitedPlainTime___closed__17_once, _init_l_Std_Time_instInhabitedPlainTime___closed__17);
v___x_196_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__9, &l_Std_Time_instInhabitedPlainTime___closed__9_once, _init_l_Std_Time_instInhabitedPlainTime___closed__9);
v___x_197_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
lean_ctor_set(v___x_197_, 2, v___x_194_);
lean_ctor_set(v___x_197_, 3, v___x_193_);
return v___x_197_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__19, &l_Std_Time_instInhabitedPlainTime___closed__19_once, _init_l_Std_Time_instInhabitedPlainTime___closed__19);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__0(lean_object* v_x_199_){
_start:
{
lean_object* v_hour_200_; 
v_hour_200_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_hour_200_);
return v_hour_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__0___boxed(lean_object* v_x_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Time_instOrdPlainTime___lam__0(v_x_201_);
lean_dec_ref(v_x_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__1(lean_object* v_x_203_){
_start:
{
lean_object* v_minute_204_; 
v_minute_204_ = lean_ctor_get(v_x_203_, 1);
lean_inc(v_minute_204_);
return v_minute_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__1___boxed(lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Time_instOrdPlainTime___lam__1(v_x_205_);
lean_dec_ref(v_x_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__2(lean_object* v_x_207_){
_start:
{
lean_object* v_second_208_; 
v_second_208_ = lean_ctor_get(v_x_207_, 2);
lean_inc(v_second_208_);
return v_second_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__2___boxed(lean_object* v_x_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Time_instOrdPlainTime___lam__2(v_x_209_);
lean_dec_ref(v_x_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__3(lean_object* v_x_211_){
_start:
{
lean_object* v_nanosecond_212_; 
v_nanosecond_212_ = lean_ctor_get(v_x_211_, 3);
lean_inc(v_nanosecond_212_);
return v_nanosecond_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__3___boxed(lean_object* v_x_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Time_instOrdPlainTime___lam__3(v_x_213_);
lean_dec_ref(v_x_213_);
return v_res_214_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__0(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_unsigned_to_nat(23u);
v___x_248_ = lean_nat_to_int(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__1(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__0, &l_Std_Time_PlainTime_midnight___closed__0_once, _init_l_Std_Time_PlainTime_midnight___closed__0);
v___x_250_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_251_ = lean_int_add(v___x_250_, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_253_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__1, &l_Std_Time_PlainTime_midnight___closed__1_once, _init_l_Std_Time_PlainTime_midnight___closed__1);
v___x_254_ = lean_int_sub(v___x_253_, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__3(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_range_257_; 
v___x_255_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_256_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__2, &l_Std_Time_PlainTime_midnight___closed__2_once, _init_l_Std_Time_PlainTime_midnight___closed__2);
v_range_257_ = lean_int_add(v___x_256_, v___x_255_);
return v_range_257_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__4(void){
_start:
{
lean_object* v_range_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_range_258_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_259_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_260_ = lean_int_emod(v___x_259_, v_range_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__5(void){
_start:
{
lean_object* v_range_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_range_261_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_262_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__4, &l_Std_Time_PlainTime_midnight___closed__4_once, _init_l_Std_Time_PlainTime_midnight___closed__4);
v___x_263_ = lean_int_add(v___x_262_, v_range_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__6(void){
_start:
{
lean_object* v_range_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_range_264_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_265_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__5, &l_Std_Time_PlainTime_midnight___closed__5_once, _init_l_Std_Time_PlainTime_midnight___closed__5);
v___x_266_ = lean_int_emod(v___x_265_, v_range_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__7(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_268_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__6, &l_Std_Time_PlainTime_midnight___closed__6_once, _init_l_Std_Time_PlainTime_midnight___closed__6);
v___x_269_ = lean_int_add(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__8(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_unsigned_to_nat(59u);
v___x_271_ = lean_nat_to_int(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__9(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__8, &l_Std_Time_PlainTime_midnight___closed__8_once, _init_l_Std_Time_PlainTime_midnight___closed__8);
v___x_273_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_274_ = lean_int_add(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__10(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_276_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__9, &l_Std_Time_PlainTime_midnight___closed__9_once, _init_l_Std_Time_PlainTime_midnight___closed__9);
v___x_277_ = lean_int_sub(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__11(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_range_280_; 
v___x_278_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_279_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__10, &l_Std_Time_PlainTime_midnight___closed__10_once, _init_l_Std_Time_PlainTime_midnight___closed__10);
v_range_280_ = lean_int_add(v___x_279_, v___x_278_);
return v_range_280_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__12(void){
_start:
{
lean_object* v_range_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_range_281_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_282_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_283_ = lean_int_emod(v___x_282_, v_range_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__13(void){
_start:
{
lean_object* v_range_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_range_284_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_285_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__12, &l_Std_Time_PlainTime_midnight___closed__12_once, _init_l_Std_Time_PlainTime_midnight___closed__12);
v___x_286_ = lean_int_add(v___x_285_, v_range_284_);
return v___x_286_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__14(void){
_start:
{
lean_object* v_range_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_range_287_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_288_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__13, &l_Std_Time_PlainTime_midnight___closed__13_once, _init_l_Std_Time_PlainTime_midnight___closed__13);
v___x_289_ = lean_int_emod(v___x_288_, v_range_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__15(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_291_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__14, &l_Std_Time_PlainTime_midnight___closed__14_once, _init_l_Std_Time_PlainTime_midnight___closed__14);
v___x_292_ = lean_int_add(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__16(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_293_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_294_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__18, &l_Std_Time_instInhabitedPlainTime___closed__18_once, _init_l_Std_Time_instInhabitedPlainTime___closed__18);
v___x_295_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__15, &l_Std_Time_PlainTime_midnight___closed__15_once, _init_l_Std_Time_PlainTime_midnight___closed__15);
v___x_296_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__7, &l_Std_Time_PlainTime_midnight___closed__7_once, _init_l_Std_Time_PlainTime_midnight___closed__7);
v___x_297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
lean_ctor_set(v___x_297_, 3, v___x_293_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight(void){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__16, &l_Std_Time_PlainTime_midnight___closed__16_once, _init_l_Std_Time_PlainTime_midnight___closed__16);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSecondsNano(lean_object* v_hour_299_, lean_object* v_minute_300_, lean_object* v_second_301_, lean_object* v_nano_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_303_, 0, v_hour_299_);
lean_ctor_set(v___x_303_, 1, v_minute_300_);
lean_ctor_set(v___x_303_, 2, v_second_301_);
lean_ctor_set(v___x_303_, 3, v_nano_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_nat_to_int(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSeconds(lean_object* v_hour_306_, lean_object* v_minute_307_, lean_object* v_second_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_obj_once(&l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0, &l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once, _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0);
v___x_310_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_310_, 0, v_hour_306_);
lean_ctor_set(v___x_310_, 1, v_minute_307_);
lean_ctor_set(v___x_310_, 2, v_second_308_);
lean_ctor_set(v___x_310_, 3, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__1(lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Rat_ofInt(v_a_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(3600000u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(60000u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(1000u);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__3(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1000000u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object* v_time_321_){
_start:
{
lean_object* v_hour_322_; lean_object* v_minute_323_; lean_object* v_second_324_; lean_object* v_nanosecond_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_hour_322_ = lean_ctor_get(v_time_321_, 0);
v_minute_323_ = lean_ctor_get(v_time_321_, 1);
v_second_324_ = lean_ctor_get(v_time_321_, 2);
v_nanosecond_325_ = lean_ctor_get(v_time_321_, 3);
v___x_326_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__0, &l_Std_Time_PlainTime_toMilliseconds___closed__0_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__0);
v___x_327_ = lean_int_mul(v_hour_322_, v___x_326_);
v___x_328_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__1, &l_Std_Time_PlainTime_toMilliseconds___closed__1_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__1);
v___x_329_ = lean_int_mul(v_minute_323_, v___x_328_);
v___x_330_ = lean_int_add(v___x_327_, v___x_329_);
lean_dec(v___x_329_);
lean_dec(v___x_327_);
v___x_331_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__2, &l_Std_Time_PlainTime_toMilliseconds___closed__2_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__2);
v___x_332_ = lean_int_mul(v_second_324_, v___x_331_);
v___x_333_ = lean_int_add(v___x_330_, v___x_332_);
lean_dec(v___x_332_);
lean_dec(v___x_330_);
v___x_334_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_335_ = lean_int_div(v_nanosecond_325_, v___x_334_);
v___x_336_ = lean_int_add(v___x_333_, v___x_335_);
lean_dec(v___x_335_);
lean_dec(v___x_333_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds___boxed(lean_object* v_time_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Time_PlainTime_toMilliseconds(v_time_337_);
lean_dec_ref(v_time_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__0(lean_object* v_a_339_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_nat_to_int(v_a_339_);
v___x_341_ = l_Rat_ofInt(v___x_340_);
return v___x_341_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_cstr_to_nat("3600000000000");
v___x_343_ = lean_nat_to_int(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_cstr_to_nat("60000000000");
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__2(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1000000000u);
v___x_347_ = lean_nat_to_int(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object* v_time_348_){
_start:
{
lean_object* v_hour_349_; lean_object* v_minute_350_; lean_object* v_second_351_; lean_object* v_nanosecond_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_hour_349_ = lean_ctor_get(v_time_348_, 0);
v_minute_350_ = lean_ctor_get(v_time_348_, 1);
v_second_351_ = lean_ctor_get(v_time_348_, 2);
v_nanosecond_352_ = lean_ctor_get(v_time_348_, 3);
v___x_353_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_354_ = lean_int_mul(v_hour_349_, v___x_353_);
v___x_355_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_356_ = lean_int_mul(v_minute_350_, v___x_355_);
v___x_357_ = lean_int_add(v___x_354_, v___x_356_);
lean_dec(v___x_356_);
lean_dec(v___x_354_);
v___x_358_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_359_ = lean_int_mul(v_second_351_, v___x_358_);
v___x_360_ = lean_int_add(v___x_357_, v___x_359_);
lean_dec(v___x_359_);
lean_dec(v___x_357_);
v___x_361_ = lean_int_add(v___x_360_, v_nanosecond_352_);
lean_dec(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds___boxed(lean_object* v_time_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_Time_PlainTime_toNanoseconds(v_time_362_);
lean_dec_ref(v_time_362_);
return v_res_363_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_unsigned_to_nat(3600u);
v___x_365_ = lean_nat_to_int(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toSeconds___closed__1(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(60u);
v___x_367_ = lean_nat_to_int(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds(lean_object* v_time_368_){
_start:
{
lean_object* v_hour_369_; lean_object* v_minute_370_; lean_object* v_second_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_hour_369_ = lean_ctor_get(v_time_368_, 0);
v_minute_370_ = lean_ctor_get(v_time_368_, 1);
v_second_371_ = lean_ctor_get(v_time_368_, 2);
v___x_372_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__0, &l_Std_Time_PlainTime_toSeconds___closed__0_once, _init_l_Std_Time_PlainTime_toSeconds___closed__0);
v___x_373_ = lean_int_mul(v_hour_369_, v___x_372_);
v___x_374_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v___x_375_ = lean_int_mul(v_minute_370_, v___x_374_);
v___x_376_ = lean_int_add(v___x_373_, v___x_375_);
lean_dec(v___x_375_);
lean_dec(v___x_373_);
v___x_377_ = lean_int_add(v___x_376_, v_second_371_);
lean_dec(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds___boxed(lean_object* v_time_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Time_PlainTime_toSeconds(v_time_378_);
lean_dec_ref(v_time_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes(lean_object* v_time_380_){
_start:
{
lean_object* v_hour_381_; lean_object* v_minute_382_; lean_object* v_second_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_hour_381_ = lean_ctor_get(v_time_380_, 0);
v_minute_382_ = lean_ctor_get(v_time_380_, 1);
v_second_383_ = lean_ctor_get(v_time_380_, 2);
v___x_384_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v___x_385_ = lean_int_mul(v_hour_381_, v___x_384_);
v___x_386_ = lean_int_add(v___x_385_, v_minute_382_);
lean_dec(v___x_385_);
v___x_387_ = lean_int_div(v_second_383_, v___x_384_);
v___x_388_ = lean_int_add(v___x_386_, v___x_387_);
lean_dec(v___x_387_);
lean_dec(v___x_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes___boxed(lean_object* v_time_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Time_PlainTime_toMinutes(v_time_389_);
lean_dec_ref(v_time_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toHours(lean_object* v_time_391_){
_start:
{
lean_object* v_hour_392_; 
v_hour_392_ = lean_ctor_get(v_time_391_, 0);
lean_inc(v_hour_392_);
return v_hour_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toHours___boxed(lean_object* v_time_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Time_PlainTime_toHours(v_time_393_);
lean_dec_ref(v_time_393_);
return v_res_394_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(24u);
v___x_396_ = lean_nat_to_int(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object* v_nanos_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_remainingNanos_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_hours_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_minutes_407_; lean_object* v_seconds_408_; lean_object* v___x_409_; 
v___x_398_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_399_ = lean_int_ediv(v_nanos_397_, v___x_398_);
v_remainingNanos_400_ = lean_int_emod(v_nanos_397_, v___x_398_);
v___x_401_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__0, &l_Std_Time_PlainTime_toSeconds___closed__0_once, _init_l_Std_Time_PlainTime_toSeconds___closed__0);
v___x_402_ = lean_int_ediv(v___x_399_, v___x_401_);
v___x_403_ = lean_obj_once(&l_Std_Time_PlainTime_ofNanoseconds___closed__0, &l_Std_Time_PlainTime_ofNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0);
v_hours_404_ = lean_int_emod(v___x_402_, v___x_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_int_emod(v___x_399_, v___x_401_);
v___x_406_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v_minutes_407_ = lean_int_ediv(v___x_405_, v___x_406_);
lean_dec(v___x_405_);
v_seconds_408_ = lean_int_emod(v___x_399_, v___x_406_);
lean_dec(v___x_399_);
v___x_409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_409_, 0, v_hours_404_);
lean_ctor_set(v___x_409_, 1, v_minutes_407_);
lean_ctor_set(v___x_409_, 2, v_seconds_408_);
lean_ctor_set(v___x_409_, 3, v_remainingNanos_400_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofNanoseconds___boxed(lean_object* v_nanos_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_410_);
lean_dec(v_nanos_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMilliseconds(lean_object* v_millis_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_414_ = lean_int_mul(v_millis_412_, v___x_413_);
v___x_415_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_414_);
lean_dec(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMilliseconds___boxed(lean_object* v_millis_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_Time_PlainTime_ofMilliseconds(v_millis_416_);
lean_dec(v_millis_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofSeconds(lean_object* v_secs_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_420_ = lean_int_mul(v_secs_418_, v___x_419_);
v___x_421_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_420_);
lean_dec(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofSeconds___boxed(lean_object* v_secs_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_Time_PlainTime_ofSeconds(v_secs_422_);
lean_dec(v_secs_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMinutes(lean_object* v_secs_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_426_ = lean_int_mul(v_secs_424_, v___x_425_);
v___x_427_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_426_);
lean_dec(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMinutes___boxed(lean_object* v_secs_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_Time_PlainTime_ofMinutes(v_secs_428_);
lean_dec(v_secs_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHours(lean_object* v_hour_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_432_ = lean_int_mul(v_hour_430_, v___x_431_);
v___x_433_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_432_);
lean_dec(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHours___boxed(lean_object* v_hour_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_Time_PlainTime_ofHours(v_hour_434_);
lean_dec(v_hour_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds(lean_object* v_time_436_, lean_object* v_secondsToAdd_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_totalSeconds_441_; lean_object* v___x_442_; 
v___x_438_ = l_Std_Time_PlainTime_toNanoseconds(v_time_436_);
v___x_439_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_440_ = lean_int_mul(v_secondsToAdd_437_, v___x_439_);
v_totalSeconds_441_ = lean_int_add(v___x_438_, v___x_440_);
lean_dec(v___x_440_);
lean_dec(v___x_438_);
v___x_442_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_441_);
lean_dec(v_totalSeconds_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds___boxed(lean_object* v_time_443_, lean_object* v_secondsToAdd_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_Time_PlainTime_addSeconds(v_time_443_, v_secondsToAdd_444_);
lean_dec(v_secondsToAdd_444_);
lean_dec_ref(v_time_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds(lean_object* v_time_446_, lean_object* v_secondsToSub_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v_totalSeconds_452_; lean_object* v___x_453_; 
v___x_448_ = lean_int_neg(v_secondsToSub_447_);
v___x_449_ = l_Std_Time_PlainTime_toNanoseconds(v_time_446_);
v___x_450_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_451_ = lean_int_mul(v___x_448_, v___x_450_);
lean_dec(v___x_448_);
v_totalSeconds_452_ = lean_int_add(v___x_449_, v___x_451_);
lean_dec(v___x_451_);
lean_dec(v___x_449_);
v___x_453_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_452_);
lean_dec(v_totalSeconds_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds___boxed(lean_object* v_time_454_, lean_object* v_secondsToSub_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_Time_PlainTime_subSeconds(v_time_454_, v_secondsToSub_455_);
lean_dec(v_secondsToSub_455_);
lean_dec_ref(v_time_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes(lean_object* v_time_457_, lean_object* v_minutesToAdd_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v_total_462_; lean_object* v___x_463_; 
v___x_459_ = l_Std_Time_PlainTime_toNanoseconds(v_time_457_);
v___x_460_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_461_ = lean_int_mul(v_minutesToAdd_458_, v___x_460_);
v_total_462_ = lean_int_add(v___x_459_, v___x_461_);
lean_dec(v___x_461_);
lean_dec(v___x_459_);
v___x_463_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_462_);
lean_dec(v_total_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes___boxed(lean_object* v_time_464_, lean_object* v_minutesToAdd_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_Time_PlainTime_addMinutes(v_time_464_, v_minutesToAdd_465_);
lean_dec(v_minutesToAdd_465_);
lean_dec_ref(v_time_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes(lean_object* v_time_467_, lean_object* v_minutesToSub_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_total_473_; lean_object* v___x_474_; 
v___x_469_ = lean_int_neg(v_minutesToSub_468_);
v___x_470_ = l_Std_Time_PlainTime_toNanoseconds(v_time_467_);
v___x_471_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_472_ = lean_int_mul(v___x_469_, v___x_471_);
lean_dec(v___x_469_);
v_total_473_ = lean_int_add(v___x_470_, v___x_472_);
lean_dec(v___x_472_);
lean_dec(v___x_470_);
v___x_474_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_473_);
lean_dec(v_total_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes___boxed(lean_object* v_time_475_, lean_object* v_minutesToSub_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Time_PlainTime_subMinutes(v_time_475_, v_minutesToSub_476_);
lean_dec(v_minutesToSub_476_);
lean_dec_ref(v_time_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours(lean_object* v_time_478_, lean_object* v_hoursToAdd_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v_total_483_; lean_object* v___x_484_; 
v___x_480_ = l_Std_Time_PlainTime_toNanoseconds(v_time_478_);
v___x_481_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_482_ = lean_int_mul(v_hoursToAdd_479_, v___x_481_);
v_total_483_ = lean_int_add(v___x_480_, v___x_482_);
lean_dec(v___x_482_);
lean_dec(v___x_480_);
v___x_484_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_483_);
lean_dec(v_total_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours___boxed(lean_object* v_time_485_, lean_object* v_hoursToAdd_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_Time_PlainTime_addHours(v_time_485_, v_hoursToAdd_486_);
lean_dec(v_hoursToAdd_486_);
lean_dec_ref(v_time_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours(lean_object* v_time_488_, lean_object* v_hoursToSub_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_total_494_; lean_object* v___x_495_; 
v___x_490_ = lean_int_neg(v_hoursToSub_489_);
v___x_491_ = l_Std_Time_PlainTime_toNanoseconds(v_time_488_);
v___x_492_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_493_ = lean_int_mul(v___x_490_, v___x_492_);
lean_dec(v___x_490_);
v_total_494_ = lean_int_add(v___x_491_, v___x_493_);
lean_dec(v___x_493_);
lean_dec(v___x_491_);
v___x_495_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_494_);
lean_dec(v_total_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours___boxed(lean_object* v_time_496_, lean_object* v_hoursToSub_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_Time_PlainTime_subHours(v_time_496_, v_hoursToSub_497_);
lean_dec(v_hoursToSub_497_);
lean_dec_ref(v_time_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds(lean_object* v_time_499_, lean_object* v_nanosToAdd_500_){
_start:
{
lean_object* v___x_501_; lean_object* v_total_502_; lean_object* v___x_503_; 
v___x_501_ = l_Std_Time_PlainTime_toNanoseconds(v_time_499_);
v_total_502_ = lean_int_add(v___x_501_, v_nanosToAdd_500_);
lean_dec(v___x_501_);
v___x_503_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_502_);
lean_dec(v_total_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds___boxed(lean_object* v_time_504_, lean_object* v_nanosToAdd_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_Time_PlainTime_addNanoseconds(v_time_504_, v_nanosToAdd_505_);
lean_dec(v_nanosToAdd_505_);
lean_dec_ref(v_time_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds(lean_object* v_time_507_, lean_object* v_nanosToSub_508_){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_509_ = lean_int_neg(v_nanosToSub_508_);
v___x_510_ = l_Std_Time_PlainTime_addNanoseconds(v_time_507_, v___x_509_);
lean_dec(v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds___boxed(lean_object* v_time_511_, lean_object* v_nanosToSub_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_Time_PlainTime_subNanoseconds(v_time_511_, v_nanosToSub_512_);
lean_dec(v_nanosToSub_512_);
lean_dec_ref(v_time_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds(lean_object* v_time_514_, lean_object* v_millisToAdd_515_){
_start:
{
lean_object* v___x_516_; lean_object* v_total_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_516_ = l_Std_Time_PlainTime_toMilliseconds(v_time_514_);
v_total_517_ = lean_int_add(v___x_516_, v_millisToAdd_515_);
lean_dec(v___x_516_);
v___x_518_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_519_ = lean_int_mul(v_total_517_, v___x_518_);
lean_dec(v_total_517_);
v___x_520_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_519_);
lean_dec(v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds___boxed(lean_object* v_time_521_, lean_object* v_millisToAdd_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Time_PlainTime_addMilliseconds(v_time_521_, v_millisToAdd_522_);
lean_dec(v_millisToAdd_522_);
lean_dec_ref(v_time_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds(lean_object* v_time_524_, lean_object* v_millisToSub_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_int_neg(v_millisToSub_525_);
v___x_527_ = l_Std_Time_PlainTime_addMilliseconds(v_time_524_, v___x_526_);
lean_dec(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds___boxed(lean_object* v_time_528_, lean_object* v_millisToSub_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_Time_PlainTime_subMilliseconds(v_time_528_, v_millisToSub_529_);
lean_dec(v_millisToSub_529_);
lean_dec_ref(v_time_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withSeconds(lean_object* v_pt_531_, lean_object* v_second_532_){
_start:
{
lean_object* v_hour_533_; lean_object* v_minute_534_; lean_object* v_nanosecond_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_hour_533_ = lean_ctor_get(v_pt_531_, 0);
v_minute_534_ = lean_ctor_get(v_pt_531_, 1);
v_nanosecond_535_ = lean_ctor_get(v_pt_531_, 3);
v_isSharedCheck_542_ = !lean_is_exclusive(v_pt_531_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; 
v_unused_543_ = lean_ctor_get(v_pt_531_, 2);
lean_dec(v_unused_543_);
v___x_537_ = v_pt_531_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_nanosecond_535_);
lean_inc(v_minute_534_);
lean_inc(v_hour_533_);
lean_dec(v_pt_531_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 2, v_second_532_);
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_hour_533_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_minute_534_);
lean_ctor_set(v_reuseFailAlloc_541_, 2, v_second_532_);
lean_ctor_set(v_reuseFailAlloc_541_, 3, v_nanosecond_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMinutes(lean_object* v_pt_544_, lean_object* v_minute_545_){
_start:
{
lean_object* v_hour_546_; lean_object* v_second_547_; lean_object* v_nanosecond_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_hour_546_ = lean_ctor_get(v_pt_544_, 0);
v_second_547_ = lean_ctor_get(v_pt_544_, 2);
v_nanosecond_548_ = lean_ctor_get(v_pt_544_, 3);
v_isSharedCheck_555_ = !lean_is_exclusive(v_pt_544_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_pt_544_, 1);
lean_dec(v_unused_556_);
v___x_550_ = v_pt_544_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_nanosecond_548_);
lean_inc(v_second_547_);
lean_inc(v_hour_546_);
lean_dec(v_pt_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_minute_545_);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_hour_546_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_minute_545_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_second_547_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_nanosecond_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds(lean_object* v_pt_557_, lean_object* v_millis_558_){
_start:
{
lean_object* v_hour_559_; lean_object* v_minute_560_; lean_object* v_second_561_; lean_object* v_nanosecond_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_574_; 
v_hour_559_ = lean_ctor_get(v_pt_557_, 0);
v_minute_560_ = lean_ctor_get(v_pt_557_, 1);
v_second_561_ = lean_ctor_get(v_pt_557_, 2);
v_nanosecond_562_ = lean_ctor_get(v_pt_557_, 3);
v_isSharedCheck_574_ = !lean_is_exclusive(v_pt_557_);
if (v_isSharedCheck_574_ == 0)
{
v___x_564_ = v_pt_557_;
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_nanosecond_562_);
lean_inc(v_second_561_);
lean_inc(v_minute_560_);
lean_inc(v_hour_559_);
lean_dec(v_pt_557_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_566_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__2, &l_Std_Time_PlainTime_toMilliseconds___closed__2_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__2);
v___x_567_ = lean_int_emod(v_nanosecond_562_, v___x_566_);
lean_dec(v_nanosecond_562_);
v___x_568_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_569_ = lean_int_mul(v_millis_558_, v___x_568_);
v___x_570_ = lean_int_add(v___x_569_, v___x_567_);
lean_dec(v___x_567_);
lean_dec(v___x_569_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 3, v___x_570_);
v___x_572_ = v___x_564_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_hour_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_minute_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_second_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds___boxed(lean_object* v_pt_575_, lean_object* v_millis_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Time_PlainTime_withMilliseconds(v_pt_575_, v_millis_576_);
lean_dec(v_millis_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withNanoseconds(lean_object* v_pt_578_, lean_object* v_nano_579_){
_start:
{
lean_object* v_hour_580_; lean_object* v_minute_581_; lean_object* v_second_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
v_hour_580_ = lean_ctor_get(v_pt_578_, 0);
v_minute_581_ = lean_ctor_get(v_pt_578_, 1);
v_second_582_ = lean_ctor_get(v_pt_578_, 2);
v_isSharedCheck_589_ = !lean_is_exclusive(v_pt_578_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v_pt_578_, 3);
lean_dec(v_unused_590_);
v___x_584_ = v_pt_578_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_second_582_);
lean_inc(v_minute_581_);
lean_inc(v_hour_580_);
lean_dec(v_pt_578_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 3, v_nano_579_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_hour_580_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_minute_581_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_second_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_nano_579_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withHours(lean_object* v_pt_591_, lean_object* v_hour_592_){
_start:
{
lean_object* v_minute_593_; lean_object* v_second_594_; lean_object* v_nanosecond_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_minute_593_ = lean_ctor_get(v_pt_591_, 1);
v_second_594_ = lean_ctor_get(v_pt_591_, 2);
v_nanosecond_595_ = lean_ctor_get(v_pt_591_, 3);
v_isSharedCheck_602_ = !lean_is_exclusive(v_pt_591_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; 
v_unused_603_ = lean_ctor_get(v_pt_591_, 0);
lean_dec(v_unused_603_);
v___x_597_ = v_pt_591_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_nanosecond_595_);
lean_inc(v_second_594_);
lean_inc(v_minute_593_);
lean_dec(v_pt_591_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v_hour_592_);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_hour_592_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_minute_593_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_second_594_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_nanosecond_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond(lean_object* v_pt_604_){
_start:
{
lean_object* v_nanosecond_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_nanosecond_605_ = lean_ctor_get(v_pt_604_, 3);
v___x_606_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_607_ = lean_int_ediv(v_nanosecond_605_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond___boxed(lean_object* v_pt_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Time_PlainTime_millisecond(v_pt_608_);
lean_dec_ref(v_pt_608_);
return v_res_609_;
}
}
lean_object* runtime_initialize_Std_Time_Time_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Time_PlainTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Time_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedPlainTime = _init_l_Std_Time_instInhabitedPlainTime();
lean_mark_persistent(l_Std_Time_instInhabitedPlainTime);
l_Std_Time_PlainTime_midnight = _init_l_Std_Time_PlainTime_midnight();
lean_mark_persistent(l_Std_Time_PlainTime_midnight);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Time_PlainTime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Time_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Time_PlainTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Time_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Time_PlainTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Time_PlainTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Time_PlainTime(builtin);
}
#ifdef __cplusplus
}
#endif
