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
uint8_t l_Std_Time_instDecidableEqPlainTime_decEq(lean_object* v_x_115_, lean_object* v_x_116_){
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
LEAN_EXPORT void l_Std_Time_instDecidableEqPlainTime_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_115_ = stack[0].m_obj;
lean_object* v_x_116_ = stack[1].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_115_, v_x_116_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainTime_decEq___boxed(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_130_, v_x_131_);
lean_dec_ref(v_x_131_);
lean_dec_ref(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
uint8_t l_Std_Time_instDecidableEqPlainTime(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_x_134_, v_x_135_);
return v___x_136_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqPlainTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_134_ = stack[0].m_obj;
lean_object* v_x_135_ = stack[1].m_obj;
uint8_t v_res_137_;
v_res_137_ = l_Std_Time_instDecidableEqPlainTime(v_x_134_, v_x_135_);
stack->m_num = v_res_137_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqPlainTime___boxed(lean_object* v_x_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_Time_instDecidableEqPlainTime(v_x_138_, v_x_139_);
lean_dec_ref(v_x_139_);
lean_dec_ref(v_x_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__0(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(23u);
v___x_143_ = lean_nat_to_int(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__1(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__0, &l_Std_Time_instInhabitedPlainTime___closed__0_once, _init_l_Std_Time_instInhabitedPlainTime___closed__0);
v___x_145_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_146_ = lean_int_add(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__2(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_148_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__1, &l_Std_Time_instInhabitedPlainTime___closed__1_once, _init_l_Std_Time_instInhabitedPlainTime___closed__1);
v___x_149_ = lean_int_sub(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__3(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_to_int(v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__4(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_range_154_; 
v___x_152_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_153_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__2, &l_Std_Time_instInhabitedPlainTime___closed__2_once, _init_l_Std_Time_instInhabitedPlainTime___closed__2);
v_range_154_ = lean_int_add(v___x_153_, v___x_152_);
return v_range_154_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__5(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_156_ = lean_int_sub(v___x_155_, v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__6(void){
_start:
{
lean_object* v_range_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_range_157_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__4, &l_Std_Time_instInhabitedPlainTime___closed__4_once, _init_l_Std_Time_instInhabitedPlainTime___closed__4);
v___x_158_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_159_ = lean_int_emod(v___x_158_, v_range_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__7(void){
_start:
{
lean_object* v_range_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_range_160_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__4, &l_Std_Time_instInhabitedPlainTime___closed__4_once, _init_l_Std_Time_instInhabitedPlainTime___closed__4);
v___x_161_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__6, &l_Std_Time_instInhabitedPlainTime___closed__6_once, _init_l_Std_Time_instInhabitedPlainTime___closed__6);
v___x_162_ = lean_int_add(v___x_161_, v_range_160_);
return v___x_162_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__8(void){
_start:
{
lean_object* v_range_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_range_163_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__4, &l_Std_Time_instInhabitedPlainTime___closed__4_once, _init_l_Std_Time_instInhabitedPlainTime___closed__4);
v___x_164_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__7, &l_Std_Time_instInhabitedPlainTime___closed__7_once, _init_l_Std_Time_instInhabitedPlainTime___closed__7);
v___x_165_ = lean_int_emod(v___x_164_, v_range_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__9(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_167_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__8, &l_Std_Time_instInhabitedPlainTime___closed__8_once, _init_l_Std_Time_instInhabitedPlainTime___closed__8);
v___x_168_ = lean_int_add(v___x_167_, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__10(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(59u);
v___x_170_ = lean_nat_to_int(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__11(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__10, &l_Std_Time_instInhabitedPlainTime___closed__10_once, _init_l_Std_Time_instInhabitedPlainTime___closed__10);
v___x_172_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_173_ = lean_int_add(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__12(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_175_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__11, &l_Std_Time_instInhabitedPlainTime___closed__11_once, _init_l_Std_Time_instInhabitedPlainTime___closed__11);
v___x_176_ = lean_int_sub(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__13(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_range_179_; 
v___x_177_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_178_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__12, &l_Std_Time_instInhabitedPlainTime___closed__12_once, _init_l_Std_Time_instInhabitedPlainTime___closed__12);
v_range_179_ = lean_int_add(v___x_178_, v___x_177_);
return v_range_179_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__14(void){
_start:
{
lean_object* v_range_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_range_180_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__13, &l_Std_Time_instInhabitedPlainTime___closed__13_once, _init_l_Std_Time_instInhabitedPlainTime___closed__13);
v___x_181_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_182_ = lean_int_emod(v___x_181_, v_range_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__15(void){
_start:
{
lean_object* v_range_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_range_183_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__13, &l_Std_Time_instInhabitedPlainTime___closed__13_once, _init_l_Std_Time_instInhabitedPlainTime___closed__13);
v___x_184_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__14, &l_Std_Time_instInhabitedPlainTime___closed__14_once, _init_l_Std_Time_instInhabitedPlainTime___closed__14);
v___x_185_ = lean_int_add(v___x_184_, v_range_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__16(void){
_start:
{
lean_object* v_range_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_range_186_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__13, &l_Std_Time_instInhabitedPlainTime___closed__13_once, _init_l_Std_Time_instInhabitedPlainTime___closed__13);
v___x_187_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__15, &l_Std_Time_instInhabitedPlainTime___closed__15_once, _init_l_Std_Time_instInhabitedPlainTime___closed__15);
v___x_188_ = lean_int_emod(v___x_187_, v_range_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__17(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_190_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__16, &l_Std_Time_instInhabitedPlainTime___closed__16_once, _init_l_Std_Time_instInhabitedPlainTime___closed__16);
v___x_191_ = lean_int_add(v___x_190_, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__18(void){
_start:
{
lean_object* v___x_192_; uint8_t v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = 1;
v___x_194_ = l_Std_Time_Second_instOfNatOrdinal(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime___closed__19(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_195_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_196_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__18, &l_Std_Time_instInhabitedPlainTime___closed__18_once, _init_l_Std_Time_instInhabitedPlainTime___closed__18);
v___x_197_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__17, &l_Std_Time_instInhabitedPlainTime___closed__17_once, _init_l_Std_Time_instInhabitedPlainTime___closed__17);
v___x_198_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__9, &l_Std_Time_instInhabitedPlainTime___closed__9_once, _init_l_Std_Time_instInhabitedPlainTime___closed__9);
v___x_199_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
lean_ctor_set(v___x_199_, 2, v___x_196_);
lean_ctor_set(v___x_199_, 3, v___x_195_);
return v___x_199_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedPlainTime(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__19, &l_Std_Time_instInhabitedPlainTime___closed__19_once, _init_l_Std_Time_instInhabitedPlainTime___closed__19);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__0(lean_object* v_x_201_){
_start:
{
lean_object* v_hour_202_; 
v_hour_202_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_hour_202_);
return v_hour_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__0___boxed(lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_Time_instOrdPlainTime___lam__0(v_x_203_);
lean_dec_ref(v_x_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__1(lean_object* v_x_205_){
_start:
{
lean_object* v_minute_206_; 
v_minute_206_ = lean_ctor_get(v_x_205_, 1);
lean_inc(v_minute_206_);
return v_minute_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__1___boxed(lean_object* v_x_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Time_instOrdPlainTime___lam__1(v_x_207_);
lean_dec_ref(v_x_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__2(lean_object* v_x_209_){
_start:
{
lean_object* v_second_210_; 
v_second_210_ = lean_ctor_get(v_x_209_, 2);
lean_inc(v_second_210_);
return v_second_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__2___boxed(lean_object* v_x_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_Time_instOrdPlainTime___lam__2(v_x_211_);
lean_dec_ref(v_x_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__3(lean_object* v_x_213_){
_start:
{
lean_object* v_nanosecond_214_; 
v_nanosecond_214_ = lean_ctor_get(v_x_213_, 3);
lean_inc(v_nanosecond_214_);
return v_nanosecond_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime___lam__3___boxed(lean_object* v_x_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_Time_instOrdPlainTime___lam__3(v_x_215_);
lean_dec_ref(v_x_215_);
return v_res_216_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__0(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(23u);
v___x_250_ = lean_nat_to_int(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__1(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__0, &l_Std_Time_PlainTime_midnight___closed__0_once, _init_l_Std_Time_PlainTime_midnight___closed__0);
v___x_252_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_253_ = lean_int_add(v___x_252_, v___x_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__2(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_255_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__1, &l_Std_Time_PlainTime_midnight___closed__1_once, _init_l_Std_Time_PlainTime_midnight___closed__1);
v___x_256_ = lean_int_sub(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__3(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v_range_259_; 
v___x_257_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_258_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__2, &l_Std_Time_PlainTime_midnight___closed__2_once, _init_l_Std_Time_PlainTime_midnight___closed__2);
v_range_259_ = lean_int_add(v___x_258_, v___x_257_);
return v_range_259_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__4(void){
_start:
{
lean_object* v_range_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_range_260_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_261_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_262_ = lean_int_emod(v___x_261_, v_range_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__5(void){
_start:
{
lean_object* v_range_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_range_263_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_264_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__4, &l_Std_Time_PlainTime_midnight___closed__4_once, _init_l_Std_Time_PlainTime_midnight___closed__4);
v___x_265_ = lean_int_add(v___x_264_, v_range_263_);
return v___x_265_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__6(void){
_start:
{
lean_object* v_range_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_range_266_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_267_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__5, &l_Std_Time_PlainTime_midnight___closed__5_once, _init_l_Std_Time_PlainTime_midnight___closed__5);
v___x_268_ = lean_int_emod(v___x_267_, v_range_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__7(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_270_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__6, &l_Std_Time_PlainTime_midnight___closed__6_once, _init_l_Std_Time_PlainTime_midnight___closed__6);
v___x_271_ = lean_int_add(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__8(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_unsigned_to_nat(59u);
v___x_273_ = lean_nat_to_int(v___x_272_);
return v___x_273_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__9(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__8, &l_Std_Time_PlainTime_midnight___closed__8_once, _init_l_Std_Time_PlainTime_midnight___closed__8);
v___x_275_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_276_ = lean_int_add(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__10(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_278_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__9, &l_Std_Time_PlainTime_midnight___closed__9_once, _init_l_Std_Time_PlainTime_midnight___closed__9);
v___x_279_ = lean_int_sub(v___x_278_, v___x_277_);
return v___x_279_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__11(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_range_282_; 
v___x_280_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_281_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__10, &l_Std_Time_PlainTime_midnight___closed__10_once, _init_l_Std_Time_PlainTime_midnight___closed__10);
v_range_282_ = lean_int_add(v___x_281_, v___x_280_);
return v_range_282_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__12(void){
_start:
{
lean_object* v_range_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_range_283_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_284_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_285_ = lean_int_emod(v___x_284_, v_range_283_);
return v___x_285_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__13(void){
_start:
{
lean_object* v_range_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_range_286_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_287_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__12, &l_Std_Time_PlainTime_midnight___closed__12_once, _init_l_Std_Time_PlainTime_midnight___closed__12);
v___x_288_ = lean_int_add(v___x_287_, v_range_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__14(void){
_start:
{
lean_object* v_range_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_range_289_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_290_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__13, &l_Std_Time_PlainTime_midnight___closed__13_once, _init_l_Std_Time_PlainTime_midnight___closed__13);
v___x_291_ = lean_int_emod(v___x_290_, v_range_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__15(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_293_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__14, &l_Std_Time_PlainTime_midnight___closed__14_once, _init_l_Std_Time_PlainTime_midnight___closed__14);
v___x_294_ = lean_int_add(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__16(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_295_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_296_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__18, &l_Std_Time_instInhabitedPlainTime___closed__18_once, _init_l_Std_Time_instInhabitedPlainTime___closed__18);
v___x_297_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__15, &l_Std_Time_PlainTime_midnight___closed__15_once, _init_l_Std_Time_PlainTime_midnight___closed__15);
v___x_298_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__7, &l_Std_Time_PlainTime_midnight___closed__7_once, _init_l_Std_Time_PlainTime_midnight___closed__7);
v___x_299_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
lean_ctor_set(v___x_299_, 2, v___x_296_);
lean_ctor_set(v___x_299_, 3, v___x_295_);
return v___x_299_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight(void){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__16, &l_Std_Time_PlainTime_midnight___closed__16_once, _init_l_Std_Time_PlainTime_midnight___closed__16);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSecondsNano(lean_object* v_hour_301_, lean_object* v_minute_302_, lean_object* v_second_303_, lean_object* v_nano_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_305_, 0, v_hour_301_);
lean_ctor_set(v___x_305_, 1, v_minute_302_);
lean_ctor_set(v___x_305_, 2, v_second_303_);
lean_ctor_set(v___x_305_, 3, v_nano_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_nat_to_int(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSeconds(lean_object* v_hour_308_, lean_object* v_minute_309_, lean_object* v_second_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_obj_once(&l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0, &l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once, _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0);
v___x_312_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_312_, 0, v_hour_308_);
lean_ctor_set(v___x_312_, 1, v_minute_309_);
lean_ctor_set(v___x_312_, 2, v_second_310_);
lean_ctor_set(v___x_312_, 3, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__1(lean_object* v_a_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Rat_ofInt(v_a_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(3600000u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(60000u);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__2(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1000u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__3(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1000000u);
v___x_322_ = lean_nat_to_int(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object* v_time_323_){
_start:
{
lean_object* v_hour_324_; lean_object* v_minute_325_; lean_object* v_second_326_; lean_object* v_nanosecond_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_hour_324_ = lean_ctor_get(v_time_323_, 0);
v_minute_325_ = lean_ctor_get(v_time_323_, 1);
v_second_326_ = lean_ctor_get(v_time_323_, 2);
v_nanosecond_327_ = lean_ctor_get(v_time_323_, 3);
v___x_328_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__0, &l_Std_Time_PlainTime_toMilliseconds___closed__0_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__0);
v___x_329_ = lean_int_mul(v_hour_324_, v___x_328_);
v___x_330_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__1, &l_Std_Time_PlainTime_toMilliseconds___closed__1_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__1);
v___x_331_ = lean_int_mul(v_minute_325_, v___x_330_);
v___x_332_ = lean_int_add(v___x_329_, v___x_331_);
lean_dec(v___x_331_);
lean_dec(v___x_329_);
v___x_333_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__2, &l_Std_Time_PlainTime_toMilliseconds___closed__2_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__2);
v___x_334_ = lean_int_mul(v_second_326_, v___x_333_);
v___x_335_ = lean_int_add(v___x_332_, v___x_334_);
lean_dec(v___x_334_);
lean_dec(v___x_332_);
v___x_336_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_337_ = lean_int_div(v_nanosecond_327_, v___x_336_);
v___x_338_ = lean_int_add(v___x_335_, v___x_337_);
lean_dec(v___x_337_);
lean_dec(v___x_335_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds___boxed(lean_object* v_time_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Time_PlainTime_toMilliseconds(v_time_339_);
lean_dec_ref(v_time_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__0(lean_object* v_a_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_nat_to_int(v_a_341_);
v___x_343_ = l_Rat_ofInt(v___x_342_);
return v___x_343_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_cstr_to_nat("3600000000000");
v___x_345_ = lean_nat_to_int(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__1(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_cstr_to_nat("60000000000");
v___x_347_ = lean_nat_to_int(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__2(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(1000000000u);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object* v_time_350_){
_start:
{
lean_object* v_hour_351_; lean_object* v_minute_352_; lean_object* v_second_353_; lean_object* v_nanosecond_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_hour_351_ = lean_ctor_get(v_time_350_, 0);
v_minute_352_ = lean_ctor_get(v_time_350_, 1);
v_second_353_ = lean_ctor_get(v_time_350_, 2);
v_nanosecond_354_ = lean_ctor_get(v_time_350_, 3);
v___x_355_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_356_ = lean_int_mul(v_hour_351_, v___x_355_);
v___x_357_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_358_ = lean_int_mul(v_minute_352_, v___x_357_);
v___x_359_ = lean_int_add(v___x_356_, v___x_358_);
lean_dec(v___x_358_);
lean_dec(v___x_356_);
v___x_360_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_361_ = lean_int_mul(v_second_353_, v___x_360_);
v___x_362_ = lean_int_add(v___x_359_, v___x_361_);
lean_dec(v___x_361_);
lean_dec(v___x_359_);
v___x_363_ = lean_int_add(v___x_362_, v_nanosecond_354_);
lean_dec(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds___boxed(lean_object* v_time_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Time_PlainTime_toNanoseconds(v_time_364_);
lean_dec_ref(v_time_364_);
return v_res_365_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_unsigned_to_nat(3600u);
v___x_367_ = lean_nat_to_int(v___x_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toSeconds___closed__1(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(60u);
v___x_369_ = lean_nat_to_int(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds(lean_object* v_time_370_){
_start:
{
lean_object* v_hour_371_; lean_object* v_minute_372_; lean_object* v_second_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_hour_371_ = lean_ctor_get(v_time_370_, 0);
v_minute_372_ = lean_ctor_get(v_time_370_, 1);
v_second_373_ = lean_ctor_get(v_time_370_, 2);
v___x_374_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__0, &l_Std_Time_PlainTime_toSeconds___closed__0_once, _init_l_Std_Time_PlainTime_toSeconds___closed__0);
v___x_375_ = lean_int_mul(v_hour_371_, v___x_374_);
v___x_376_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v___x_377_ = lean_int_mul(v_minute_372_, v___x_376_);
v___x_378_ = lean_int_add(v___x_375_, v___x_377_);
lean_dec(v___x_377_);
lean_dec(v___x_375_);
v___x_379_ = lean_int_add(v___x_378_, v_second_373_);
lean_dec(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds___boxed(lean_object* v_time_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Time_PlainTime_toSeconds(v_time_380_);
lean_dec_ref(v_time_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes(lean_object* v_time_382_){
_start:
{
lean_object* v_hour_383_; lean_object* v_minute_384_; lean_object* v_second_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_hour_383_ = lean_ctor_get(v_time_382_, 0);
v_minute_384_ = lean_ctor_get(v_time_382_, 1);
v_second_385_ = lean_ctor_get(v_time_382_, 2);
v___x_386_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v___x_387_ = lean_int_mul(v_hour_383_, v___x_386_);
v___x_388_ = lean_int_add(v___x_387_, v_minute_384_);
lean_dec(v___x_387_);
v___x_389_ = lean_int_div(v_second_385_, v___x_386_);
v___x_390_ = lean_int_add(v___x_388_, v___x_389_);
lean_dec(v___x_389_);
lean_dec(v___x_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes___boxed(lean_object* v_time_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Time_PlainTime_toMinutes(v_time_391_);
lean_dec_ref(v_time_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toHours(lean_object* v_time_393_){
_start:
{
lean_object* v_hour_394_; 
v_hour_394_ = lean_ctor_get(v_time_393_, 0);
lean_inc(v_hour_394_);
return v_hour_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toHours___boxed(lean_object* v_time_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_Time_PlainTime_toHours(v_time_395_);
lean_dec_ref(v_time_395_);
return v_res_396_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(24u);
v___x_398_ = lean_nat_to_int(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object* v_nanos_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_remainingNanos_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_hours_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_minutes_409_; lean_object* v_seconds_410_; lean_object* v___x_411_; 
v___x_400_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_401_ = lean_int_ediv(v_nanos_399_, v___x_400_);
v_remainingNanos_402_ = lean_int_emod(v_nanos_399_, v___x_400_);
v___x_403_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__0, &l_Std_Time_PlainTime_toSeconds___closed__0_once, _init_l_Std_Time_PlainTime_toSeconds___closed__0);
v___x_404_ = lean_int_ediv(v___x_401_, v___x_403_);
v___x_405_ = lean_obj_once(&l_Std_Time_PlainTime_ofNanoseconds___closed__0, &l_Std_Time_PlainTime_ofNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0);
v_hours_406_ = lean_int_emod(v___x_404_, v___x_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_int_emod(v___x_401_, v___x_403_);
v___x_408_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v_minutes_409_ = lean_int_ediv(v___x_407_, v___x_408_);
lean_dec(v___x_407_);
v_seconds_410_ = lean_int_emod(v___x_401_, v___x_408_);
lean_dec(v___x_401_);
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v_hours_406_);
lean_ctor_set(v___x_411_, 1, v_minutes_409_);
lean_ctor_set(v___x_411_, 2, v_seconds_410_);
lean_ctor_set(v___x_411_, 3, v_remainingNanos_402_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofNanoseconds___boxed(lean_object* v_nanos_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_412_);
lean_dec(v_nanos_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMilliseconds(lean_object* v_millis_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_416_ = lean_int_mul(v_millis_414_, v___x_415_);
v___x_417_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_416_);
lean_dec(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMilliseconds___boxed(lean_object* v_millis_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_Time_PlainTime_ofMilliseconds(v_millis_418_);
lean_dec(v_millis_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofSeconds(lean_object* v_secs_420_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_422_ = lean_int_mul(v_secs_420_, v___x_421_);
v___x_423_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_422_);
lean_dec(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofSeconds___boxed(lean_object* v_secs_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_Time_PlainTime_ofSeconds(v_secs_424_);
lean_dec(v_secs_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMinutes(lean_object* v_secs_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_428_ = lean_int_mul(v_secs_426_, v___x_427_);
v___x_429_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_428_);
lean_dec(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMinutes___boxed(lean_object* v_secs_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_Time_PlainTime_ofMinutes(v_secs_430_);
lean_dec(v_secs_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHours(lean_object* v_hour_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_434_ = lean_int_mul(v_hour_432_, v___x_433_);
v___x_435_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_434_);
lean_dec(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHours___boxed(lean_object* v_hour_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Time_PlainTime_ofHours(v_hour_436_);
lean_dec(v_hour_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds(lean_object* v_time_438_, lean_object* v_secondsToAdd_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_totalSeconds_443_; lean_object* v___x_444_; 
v___x_440_ = l_Std_Time_PlainTime_toNanoseconds(v_time_438_);
v___x_441_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_442_ = lean_int_mul(v_secondsToAdd_439_, v___x_441_);
v_totalSeconds_443_ = lean_int_add(v___x_440_, v___x_442_);
lean_dec(v___x_442_);
lean_dec(v___x_440_);
v___x_444_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_443_);
lean_dec(v_totalSeconds_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds___boxed(lean_object* v_time_445_, lean_object* v_secondsToAdd_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_Time_PlainTime_addSeconds(v_time_445_, v_secondsToAdd_446_);
lean_dec(v_secondsToAdd_446_);
lean_dec_ref(v_time_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds(lean_object* v_time_448_, lean_object* v_secondsToSub_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_totalSeconds_454_; lean_object* v___x_455_; 
v___x_450_ = lean_int_neg(v_secondsToSub_449_);
v___x_451_ = l_Std_Time_PlainTime_toNanoseconds(v_time_448_);
v___x_452_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_453_ = lean_int_mul(v___x_450_, v___x_452_);
lean_dec(v___x_450_);
v_totalSeconds_454_ = lean_int_add(v___x_451_, v___x_453_);
lean_dec(v___x_453_);
lean_dec(v___x_451_);
v___x_455_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_454_);
lean_dec(v_totalSeconds_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds___boxed(lean_object* v_time_456_, lean_object* v_secondsToSub_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_Time_PlainTime_subSeconds(v_time_456_, v_secondsToSub_457_);
lean_dec(v_secondsToSub_457_);
lean_dec_ref(v_time_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes(lean_object* v_time_459_, lean_object* v_minutesToAdd_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_total_464_; lean_object* v___x_465_; 
v___x_461_ = l_Std_Time_PlainTime_toNanoseconds(v_time_459_);
v___x_462_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_463_ = lean_int_mul(v_minutesToAdd_460_, v___x_462_);
v_total_464_ = lean_int_add(v___x_461_, v___x_463_);
lean_dec(v___x_463_);
lean_dec(v___x_461_);
v___x_465_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_464_);
lean_dec(v_total_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes___boxed(lean_object* v_time_466_, lean_object* v_minutesToAdd_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Time_PlainTime_addMinutes(v_time_466_, v_minutesToAdd_467_);
lean_dec(v_minutesToAdd_467_);
lean_dec_ref(v_time_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes(lean_object* v_time_469_, lean_object* v_minutesToSub_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_total_475_; lean_object* v___x_476_; 
v___x_471_ = lean_int_neg(v_minutesToSub_470_);
v___x_472_ = l_Std_Time_PlainTime_toNanoseconds(v_time_469_);
v___x_473_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_474_ = lean_int_mul(v___x_471_, v___x_473_);
lean_dec(v___x_471_);
v_total_475_ = lean_int_add(v___x_472_, v___x_474_);
lean_dec(v___x_474_);
lean_dec(v___x_472_);
v___x_476_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_475_);
lean_dec(v_total_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes___boxed(lean_object* v_time_477_, lean_object* v_minutesToSub_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Std_Time_PlainTime_subMinutes(v_time_477_, v_minutesToSub_478_);
lean_dec(v_minutesToSub_478_);
lean_dec_ref(v_time_477_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours(lean_object* v_time_480_, lean_object* v_hoursToAdd_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v_total_485_; lean_object* v___x_486_; 
v___x_482_ = l_Std_Time_PlainTime_toNanoseconds(v_time_480_);
v___x_483_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_484_ = lean_int_mul(v_hoursToAdd_481_, v___x_483_);
v_total_485_ = lean_int_add(v___x_482_, v___x_484_);
lean_dec(v___x_484_);
lean_dec(v___x_482_);
v___x_486_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_485_);
lean_dec(v_total_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours___boxed(lean_object* v_time_487_, lean_object* v_hoursToAdd_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_Time_PlainTime_addHours(v_time_487_, v_hoursToAdd_488_);
lean_dec(v_hoursToAdd_488_);
lean_dec_ref(v_time_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours(lean_object* v_time_490_, lean_object* v_hoursToSub_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_total_496_; lean_object* v___x_497_; 
v___x_492_ = lean_int_neg(v_hoursToSub_491_);
v___x_493_ = l_Std_Time_PlainTime_toNanoseconds(v_time_490_);
v___x_494_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_495_ = lean_int_mul(v___x_492_, v___x_494_);
lean_dec(v___x_492_);
v_total_496_ = lean_int_add(v___x_493_, v___x_495_);
lean_dec(v___x_495_);
lean_dec(v___x_493_);
v___x_497_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_496_);
lean_dec(v_total_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours___boxed(lean_object* v_time_498_, lean_object* v_hoursToSub_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Time_PlainTime_subHours(v_time_498_, v_hoursToSub_499_);
lean_dec(v_hoursToSub_499_);
lean_dec_ref(v_time_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds(lean_object* v_time_501_, lean_object* v_nanosToAdd_502_){
_start:
{
lean_object* v___x_503_; lean_object* v_total_504_; lean_object* v___x_505_; 
v___x_503_ = l_Std_Time_PlainTime_toNanoseconds(v_time_501_);
v_total_504_ = lean_int_add(v___x_503_, v_nanosToAdd_502_);
lean_dec(v___x_503_);
v___x_505_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_504_);
lean_dec(v_total_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds___boxed(lean_object* v_time_506_, lean_object* v_nanosToAdd_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_Time_PlainTime_addNanoseconds(v_time_506_, v_nanosToAdd_507_);
lean_dec(v_nanosToAdd_507_);
lean_dec_ref(v_time_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds(lean_object* v_time_509_, lean_object* v_nanosToSub_510_){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_int_neg(v_nanosToSub_510_);
v___x_512_ = l_Std_Time_PlainTime_addNanoseconds(v_time_509_, v___x_511_);
lean_dec(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds___boxed(lean_object* v_time_513_, lean_object* v_nanosToSub_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_Time_PlainTime_subNanoseconds(v_time_513_, v_nanosToSub_514_);
lean_dec(v_nanosToSub_514_);
lean_dec_ref(v_time_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds(lean_object* v_time_516_, lean_object* v_millisToAdd_517_){
_start:
{
lean_object* v___x_518_; lean_object* v_total_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_518_ = l_Std_Time_PlainTime_toMilliseconds(v_time_516_);
v_total_519_ = lean_int_add(v___x_518_, v_millisToAdd_517_);
lean_dec(v___x_518_);
v___x_520_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_521_ = lean_int_mul(v_total_519_, v___x_520_);
lean_dec(v_total_519_);
v___x_522_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_521_);
lean_dec(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds___boxed(lean_object* v_time_523_, lean_object* v_millisToAdd_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Time_PlainTime_addMilliseconds(v_time_523_, v_millisToAdd_524_);
lean_dec(v_millisToAdd_524_);
lean_dec_ref(v_time_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds(lean_object* v_time_526_, lean_object* v_millisToSub_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_int_neg(v_millisToSub_527_);
v___x_529_ = l_Std_Time_PlainTime_addMilliseconds(v_time_526_, v___x_528_);
lean_dec(v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds___boxed(lean_object* v_time_530_, lean_object* v_millisToSub_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Time_PlainTime_subMilliseconds(v_time_530_, v_millisToSub_531_);
lean_dec(v_millisToSub_531_);
lean_dec_ref(v_time_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withSeconds(lean_object* v_pt_533_, lean_object* v_second_534_){
_start:
{
lean_object* v_hour_535_; lean_object* v_minute_536_; lean_object* v_nanosecond_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_hour_535_ = lean_ctor_get(v_pt_533_, 0);
v_minute_536_ = lean_ctor_get(v_pt_533_, 1);
v_nanosecond_537_ = lean_ctor_get(v_pt_533_, 3);
v_isSharedCheck_544_ = !lean_is_exclusive(v_pt_533_);
if (v_isSharedCheck_544_ == 0)
{
lean_object* v_unused_545_; 
v_unused_545_ = lean_ctor_get(v_pt_533_, 2);
lean_dec(v_unused_545_);
v___x_539_ = v_pt_533_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_nanosecond_537_);
lean_inc(v_minute_536_);
lean_inc(v_hour_535_);
lean_dec(v_pt_533_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 2, v_second_534_);
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_hour_535_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_minute_536_);
lean_ctor_set(v_reuseFailAlloc_543_, 2, v_second_534_);
lean_ctor_set(v_reuseFailAlloc_543_, 3, v_nanosecond_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMinutes(lean_object* v_pt_546_, lean_object* v_minute_547_){
_start:
{
lean_object* v_hour_548_; lean_object* v_second_549_; lean_object* v_nanosecond_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_hour_548_ = lean_ctor_get(v_pt_546_, 0);
v_second_549_ = lean_ctor_get(v_pt_546_, 2);
v_nanosecond_550_ = lean_ctor_get(v_pt_546_, 3);
v_isSharedCheck_557_ = !lean_is_exclusive(v_pt_546_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v_pt_546_, 1);
lean_dec(v_unused_558_);
v___x_552_ = v_pt_546_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_nanosecond_550_);
lean_inc(v_second_549_);
lean_inc(v_hour_548_);
lean_dec(v_pt_546_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v_minute_547_);
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_hour_548_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_minute_547_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_second_549_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_nanosecond_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds(lean_object* v_pt_559_, lean_object* v_millis_560_){
_start:
{
lean_object* v_hour_561_; lean_object* v_minute_562_; lean_object* v_second_563_; lean_object* v_nanosecond_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_576_; 
v_hour_561_ = lean_ctor_get(v_pt_559_, 0);
v_minute_562_ = lean_ctor_get(v_pt_559_, 1);
v_second_563_ = lean_ctor_get(v_pt_559_, 2);
v_nanosecond_564_ = lean_ctor_get(v_pt_559_, 3);
v_isSharedCheck_576_ = !lean_is_exclusive(v_pt_559_);
if (v_isSharedCheck_576_ == 0)
{
v___x_566_ = v_pt_559_;
v_isShared_567_ = v_isSharedCheck_576_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_nanosecond_564_);
lean_inc(v_second_563_);
lean_inc(v_minute_562_);
lean_inc(v_hour_561_);
lean_dec(v_pt_559_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_576_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_568_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__2, &l_Std_Time_PlainTime_toMilliseconds___closed__2_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__2);
v___x_569_ = lean_int_emod(v_nanosecond_564_, v___x_568_);
lean_dec(v_nanosecond_564_);
v___x_570_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_571_ = lean_int_mul(v_millis_560_, v___x_570_);
v___x_572_ = lean_int_add(v___x_571_, v___x_569_);
lean_dec(v___x_569_);
lean_dec(v___x_571_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 3, v___x_572_);
v___x_574_ = v___x_566_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_hour_561_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_minute_562_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v_second_563_);
lean_ctor_set(v_reuseFailAlloc_575_, 3, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds___boxed(lean_object* v_pt_577_, lean_object* v_millis_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Time_PlainTime_withMilliseconds(v_pt_577_, v_millis_578_);
lean_dec(v_millis_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withNanoseconds(lean_object* v_pt_580_, lean_object* v_nano_581_){
_start:
{
lean_object* v_hour_582_; lean_object* v_minute_583_; lean_object* v_second_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_hour_582_ = lean_ctor_get(v_pt_580_, 0);
v_minute_583_ = lean_ctor_get(v_pt_580_, 1);
v_second_584_ = lean_ctor_get(v_pt_580_, 2);
v_isSharedCheck_591_ = !lean_is_exclusive(v_pt_580_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_pt_580_, 3);
lean_dec(v_unused_592_);
v___x_586_ = v_pt_580_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_second_584_);
lean_inc(v_minute_583_);
lean_inc(v_hour_582_);
lean_dec(v_pt_580_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 3, v_nano_581_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_hour_582_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_minute_583_);
lean_ctor_set(v_reuseFailAlloc_590_, 2, v_second_584_);
lean_ctor_set(v_reuseFailAlloc_590_, 3, v_nano_581_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withHours(lean_object* v_pt_593_, lean_object* v_hour_594_){
_start:
{
lean_object* v_minute_595_; lean_object* v_second_596_; lean_object* v_nanosecond_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_minute_595_ = lean_ctor_get(v_pt_593_, 1);
v_second_596_ = lean_ctor_get(v_pt_593_, 2);
v_nanosecond_597_ = lean_ctor_get(v_pt_593_, 3);
v_isSharedCheck_604_ = !lean_is_exclusive(v_pt_593_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; 
v_unused_605_ = lean_ctor_get(v_pt_593_, 0);
lean_dec(v_unused_605_);
v___x_599_ = v_pt_593_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_nanosecond_597_);
lean_inc(v_second_596_);
lean_inc(v_minute_595_);
lean_dec(v_pt_593_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v_hour_594_);
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_hour_594_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_minute_595_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_second_596_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_nanosecond_597_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond(lean_object* v_pt_606_){
_start:
{
lean_object* v_nanosecond_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_nanosecond_607_ = lean_ctor_get(v_pt_606_, 3);
v___x_608_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_609_ = lean_int_ediv(v_nanosecond_607_, v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond___boxed(lean_object* v_pt_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Time_PlainTime_millisecond(v_pt_610_);
lean_dec_ref(v_pt_610_);
return v_res_611_;
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
