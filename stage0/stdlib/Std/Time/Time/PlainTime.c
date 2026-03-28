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
lean_object* lean_nat_mod(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__17;
static lean_once_cell_t l_Std_Time_PlainTime_midnight___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_midnight___closed__18;
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
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(1000000000u);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_nat_mod(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__17(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__16, &l_Std_Time_PlainTime_midnight___closed__16_once, _init_l_Std_Time_PlainTime_midnight___closed__16);
v___x_297_ = lean_nat_to_int(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__18(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_298_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__17, &l_Std_Time_PlainTime_midnight___closed__17_once, _init_l_Std_Time_PlainTime_midnight___closed__17);
v___x_299_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__18, &l_Std_Time_instInhabitedPlainTime___closed__18_once, _init_l_Std_Time_instInhabitedPlainTime___closed__18);
v___x_300_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__15, &l_Std_Time_PlainTime_midnight___closed__15_once, _init_l_Std_Time_PlainTime_midnight___closed__15);
v___x_301_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__7, &l_Std_Time_PlainTime_midnight___closed__7_once, _init_l_Std_Time_PlainTime_midnight___closed__7);
v___x_302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
lean_ctor_set(v___x_302_, 3, v___x_298_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight(void){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__18, &l_Std_Time_PlainTime_midnight___closed__18_once, _init_l_Std_Time_PlainTime_midnight___closed__18);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSecondsNano(lean_object* v_hour_304_, lean_object* v_minute_305_, lean_object* v_second_306_, lean_object* v_nano_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_308_, 0, v_hour_304_);
lean_ctor_set(v___x_308_, 1, v_minute_305_);
lean_ctor_set(v___x_308_, 2, v_second_306_);
lean_ctor_set(v___x_308_, 3, v_nano_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__16, &l_Std_Time_PlainTime_midnight___closed__16_once, _init_l_Std_Time_PlainTime_midnight___closed__16);
v___x_310_ = lean_nat_to_int(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSeconds(lean_object* v_hour_311_, lean_object* v_minute_312_, lean_object* v_second_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0, &l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once, _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0);
v___x_315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_315_, 0, v_hour_311_);
lean_ctor_set(v___x_315_, 1, v_minute_312_);
lean_ctor_set(v___x_315_, 2, v_second_313_);
lean_ctor_set(v___x_315_, 3, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__1(lean_object* v_a_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Rat_ofInt(v_a_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(3600000u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(60000u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__2(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1000u);
v___x_323_ = lean_nat_to_int(v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__3(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(1000000u);
v___x_325_ = lean_nat_to_int(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object* v_time_326_){
_start:
{
lean_object* v_hour_327_; lean_object* v_minute_328_; lean_object* v_second_329_; lean_object* v_nanosecond_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_hour_327_ = lean_ctor_get(v_time_326_, 0);
v_minute_328_ = lean_ctor_get(v_time_326_, 1);
v_second_329_ = lean_ctor_get(v_time_326_, 2);
v_nanosecond_330_ = lean_ctor_get(v_time_326_, 3);
v___x_331_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__0, &l_Std_Time_PlainTime_toMilliseconds___closed__0_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__0);
v___x_332_ = lean_int_mul(v_hour_327_, v___x_331_);
v___x_333_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__1, &l_Std_Time_PlainTime_toMilliseconds___closed__1_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__1);
v___x_334_ = lean_int_mul(v_minute_328_, v___x_333_);
v___x_335_ = lean_int_add(v___x_332_, v___x_334_);
lean_dec(v___x_334_);
lean_dec(v___x_332_);
v___x_336_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__2, &l_Std_Time_PlainTime_toMilliseconds___closed__2_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__2);
v___x_337_ = lean_int_mul(v_second_329_, v___x_336_);
v___x_338_ = lean_int_add(v___x_335_, v___x_337_);
lean_dec(v___x_337_);
lean_dec(v___x_335_);
v___x_339_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_340_ = lean_int_div(v_nanosecond_330_, v___x_339_);
v___x_341_ = lean_int_add(v___x_338_, v___x_340_);
lean_dec(v___x_340_);
lean_dec(v___x_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds___boxed(lean_object* v_time_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_Time_PlainTime_toMilliseconds(v_time_342_);
lean_dec_ref(v_time_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__0(lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_nat_to_int(v_a_344_);
v___x_346_ = l_Rat_ofInt(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_cstr_to_nat("3600000000000");
v___x_348_ = lean_nat_to_int(v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__1(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_cstr_to_nat("60000000000");
v___x_350_ = lean_nat_to_int(v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__2(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(1000000000u);
v___x_352_ = lean_nat_to_int(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object* v_time_353_){
_start:
{
lean_object* v_hour_354_; lean_object* v_minute_355_; lean_object* v_second_356_; lean_object* v_nanosecond_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_hour_354_ = lean_ctor_get(v_time_353_, 0);
v_minute_355_ = lean_ctor_get(v_time_353_, 1);
v_second_356_ = lean_ctor_get(v_time_353_, 2);
v_nanosecond_357_ = lean_ctor_get(v_time_353_, 3);
v___x_358_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_359_ = lean_int_mul(v_hour_354_, v___x_358_);
v___x_360_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_361_ = lean_int_mul(v_minute_355_, v___x_360_);
v___x_362_ = lean_int_add(v___x_359_, v___x_361_);
lean_dec(v___x_361_);
lean_dec(v___x_359_);
v___x_363_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_364_ = lean_int_mul(v_second_356_, v___x_363_);
v___x_365_ = lean_int_add(v___x_362_, v___x_364_);
lean_dec(v___x_364_);
lean_dec(v___x_362_);
v___x_366_ = lean_int_add(v___x_365_, v_nanosecond_357_);
lean_dec(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds___boxed(lean_object* v_time_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_Time_PlainTime_toNanoseconds(v_time_367_);
lean_dec_ref(v_time_367_);
return v_res_368_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toSeconds___closed__0(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_unsigned_to_nat(3600u);
v___x_370_ = lean_nat_to_int(v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toSeconds___closed__1(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_unsigned_to_nat(60u);
v___x_372_ = lean_nat_to_int(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds(lean_object* v_time_373_){
_start:
{
lean_object* v_hour_374_; lean_object* v_minute_375_; lean_object* v_second_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_hour_374_ = lean_ctor_get(v_time_373_, 0);
v_minute_375_ = lean_ctor_get(v_time_373_, 1);
v_second_376_ = lean_ctor_get(v_time_373_, 2);
v___x_377_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__0, &l_Std_Time_PlainTime_toSeconds___closed__0_once, _init_l_Std_Time_PlainTime_toSeconds___closed__0);
v___x_378_ = lean_int_mul(v_hour_374_, v___x_377_);
v___x_379_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v___x_380_ = lean_int_mul(v_minute_375_, v___x_379_);
v___x_381_ = lean_int_add(v___x_378_, v___x_380_);
lean_dec(v___x_380_);
lean_dec(v___x_378_);
v___x_382_ = lean_int_add(v___x_381_, v_second_376_);
lean_dec(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds___boxed(lean_object* v_time_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Time_PlainTime_toSeconds(v_time_383_);
lean_dec_ref(v_time_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes(lean_object* v_time_385_){
_start:
{
lean_object* v_hour_386_; lean_object* v_minute_387_; lean_object* v_second_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_hour_386_ = lean_ctor_get(v_time_385_, 0);
v_minute_387_ = lean_ctor_get(v_time_385_, 1);
v_second_388_ = lean_ctor_get(v_time_385_, 2);
v___x_389_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v___x_390_ = lean_int_mul(v_hour_386_, v___x_389_);
v___x_391_ = lean_int_add(v___x_390_, v_minute_387_);
lean_dec(v___x_390_);
v___x_392_ = lean_int_div(v_second_388_, v___x_389_);
v___x_393_ = lean_int_add(v___x_391_, v___x_392_);
lean_dec(v___x_392_);
lean_dec(v___x_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes___boxed(lean_object* v_time_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_Time_PlainTime_toMinutes(v_time_394_);
lean_dec_ref(v_time_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toHours(lean_object* v_time_396_){
_start:
{
lean_object* v_hour_397_; 
v_hour_397_ = lean_ctor_get(v_time_396_, 0);
lean_inc(v_hour_397_);
return v_hour_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toHours___boxed(lean_object* v_time_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_Time_PlainTime_toHours(v_time_398_);
lean_dec_ref(v_time_398_);
return v_res_399_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_unsigned_to_nat(24u);
v___x_401_ = lean_nat_to_int(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object* v_nanos_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_remainingNanos_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v_hours_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_minutes_412_; lean_object* v_seconds_413_; lean_object* v___x_414_; 
v___x_403_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_404_ = lean_int_ediv(v_nanos_402_, v___x_403_);
v_remainingNanos_405_ = lean_int_emod(v_nanos_402_, v___x_403_);
v___x_406_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__0, &l_Std_Time_PlainTime_toSeconds___closed__0_once, _init_l_Std_Time_PlainTime_toSeconds___closed__0);
v___x_407_ = lean_int_ediv(v___x_404_, v___x_406_);
v___x_408_ = lean_obj_once(&l_Std_Time_PlainTime_ofNanoseconds___closed__0, &l_Std_Time_PlainTime_ofNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_ofNanoseconds___closed__0);
v_hours_409_ = lean_int_emod(v___x_407_, v___x_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_int_emod(v___x_404_, v___x_406_);
v___x_411_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v_minutes_412_ = lean_int_ediv(v___x_410_, v___x_411_);
lean_dec(v___x_410_);
v_seconds_413_ = lean_int_emod(v___x_404_, v___x_411_);
lean_dec(v___x_404_);
v___x_414_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_414_, 0, v_hours_409_);
lean_ctor_set(v___x_414_, 1, v_minutes_412_);
lean_ctor_set(v___x_414_, 2, v_seconds_413_);
lean_ctor_set(v___x_414_, 3, v_remainingNanos_405_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofNanoseconds___boxed(lean_object* v_nanos_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_Time_PlainTime_ofNanoseconds(v_nanos_415_);
lean_dec(v_nanos_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMilliseconds(lean_object* v_millis_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_419_ = lean_int_mul(v_millis_417_, v___x_418_);
v___x_420_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_419_);
lean_dec(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMilliseconds___boxed(lean_object* v_millis_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Std_Time_PlainTime_ofMilliseconds(v_millis_421_);
lean_dec(v_millis_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofSeconds(lean_object* v_secs_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_425_ = lean_int_mul(v_secs_423_, v___x_424_);
v___x_426_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_425_);
lean_dec(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofSeconds___boxed(lean_object* v_secs_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_Time_PlainTime_ofSeconds(v_secs_427_);
lean_dec(v_secs_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMinutes(lean_object* v_secs_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_431_ = lean_int_mul(v_secs_429_, v___x_430_);
v___x_432_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_431_);
lean_dec(v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofMinutes___boxed(lean_object* v_secs_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_Time_PlainTime_ofMinutes(v_secs_433_);
lean_dec(v_secs_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHours(lean_object* v_hour_435_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_437_ = lean_int_mul(v_hour_435_, v___x_436_);
v___x_438_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_437_);
lean_dec(v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHours___boxed(lean_object* v_hour_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_Time_PlainTime_ofHours(v_hour_439_);
lean_dec(v_hour_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds(lean_object* v_time_441_, lean_object* v_secondsToAdd_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_totalSeconds_446_; lean_object* v___x_447_; 
v___x_443_ = l_Std_Time_PlainTime_toNanoseconds(v_time_441_);
v___x_444_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_445_ = lean_int_mul(v_secondsToAdd_442_, v___x_444_);
v_totalSeconds_446_ = lean_int_add(v___x_443_, v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_443_);
v___x_447_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_446_);
lean_dec(v_totalSeconds_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds___boxed(lean_object* v_time_448_, lean_object* v_secondsToAdd_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Time_PlainTime_addSeconds(v_time_448_, v_secondsToAdd_449_);
lean_dec(v_secondsToAdd_449_);
lean_dec_ref(v_time_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds(lean_object* v_time_451_, lean_object* v_secondsToSub_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_totalSeconds_457_; lean_object* v___x_458_; 
v___x_453_ = lean_int_neg(v_secondsToSub_452_);
v___x_454_ = l_Std_Time_PlainTime_toNanoseconds(v_time_451_);
v___x_455_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_456_ = lean_int_mul(v___x_453_, v___x_455_);
lean_dec(v___x_453_);
v_totalSeconds_457_ = lean_int_add(v___x_454_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v___x_454_);
v___x_458_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_457_);
lean_dec(v_totalSeconds_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds___boxed(lean_object* v_time_459_, lean_object* v_secondsToSub_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_Time_PlainTime_subSeconds(v_time_459_, v_secondsToSub_460_);
lean_dec(v_secondsToSub_460_);
lean_dec_ref(v_time_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes(lean_object* v_time_462_, lean_object* v_minutesToAdd_463_){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_total_467_; lean_object* v___x_468_; 
v___x_464_ = l_Std_Time_PlainTime_toNanoseconds(v_time_462_);
v___x_465_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_466_ = lean_int_mul(v_minutesToAdd_463_, v___x_465_);
v_total_467_ = lean_int_add(v___x_464_, v___x_466_);
lean_dec(v___x_466_);
lean_dec(v___x_464_);
v___x_468_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_467_);
lean_dec(v_total_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes___boxed(lean_object* v_time_469_, lean_object* v_minutesToAdd_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_Time_PlainTime_addMinutes(v_time_469_, v_minutesToAdd_470_);
lean_dec(v_minutesToAdd_470_);
lean_dec_ref(v_time_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes(lean_object* v_time_472_, lean_object* v_minutesToSub_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_total_478_; lean_object* v___x_479_; 
v___x_474_ = lean_int_neg(v_minutesToSub_473_);
v___x_475_ = l_Std_Time_PlainTime_toNanoseconds(v_time_472_);
v___x_476_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_477_ = lean_int_mul(v___x_474_, v___x_476_);
lean_dec(v___x_474_);
v_total_478_ = lean_int_add(v___x_475_, v___x_477_);
lean_dec(v___x_477_);
lean_dec(v___x_475_);
v___x_479_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_478_);
lean_dec(v_total_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes___boxed(lean_object* v_time_480_, lean_object* v_minutesToSub_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Time_PlainTime_subMinutes(v_time_480_, v_minutesToSub_481_);
lean_dec(v_minutesToSub_481_);
lean_dec_ref(v_time_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours(lean_object* v_time_483_, lean_object* v_hoursToAdd_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_total_488_; lean_object* v___x_489_; 
v___x_485_ = l_Std_Time_PlainTime_toNanoseconds(v_time_483_);
v___x_486_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_487_ = lean_int_mul(v_hoursToAdd_484_, v___x_486_);
v_total_488_ = lean_int_add(v___x_485_, v___x_487_);
lean_dec(v___x_487_);
lean_dec(v___x_485_);
v___x_489_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_488_);
lean_dec(v_total_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours___boxed(lean_object* v_time_490_, lean_object* v_hoursToAdd_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Time_PlainTime_addHours(v_time_490_, v_hoursToAdd_491_);
lean_dec(v_hoursToAdd_491_);
lean_dec_ref(v_time_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours(lean_object* v_time_493_, lean_object* v_hoursToSub_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v_total_499_; lean_object* v___x_500_; 
v___x_495_ = lean_int_neg(v_hoursToSub_494_);
v___x_496_ = l_Std_Time_PlainTime_toNanoseconds(v_time_493_);
v___x_497_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_498_ = lean_int_mul(v___x_495_, v___x_497_);
lean_dec(v___x_495_);
v_total_499_ = lean_int_add(v___x_496_, v___x_498_);
lean_dec(v___x_498_);
lean_dec(v___x_496_);
v___x_500_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_499_);
lean_dec(v_total_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours___boxed(lean_object* v_time_501_, lean_object* v_hoursToSub_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_Time_PlainTime_subHours(v_time_501_, v_hoursToSub_502_);
lean_dec(v_hoursToSub_502_);
lean_dec_ref(v_time_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds(lean_object* v_time_504_, lean_object* v_nanosToAdd_505_){
_start:
{
lean_object* v___x_506_; lean_object* v_total_507_; lean_object* v___x_508_; 
v___x_506_ = l_Std_Time_PlainTime_toNanoseconds(v_time_504_);
v_total_507_ = lean_int_add(v___x_506_, v_nanosToAdd_505_);
lean_dec(v___x_506_);
v___x_508_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_507_);
lean_dec(v_total_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds___boxed(lean_object* v_time_509_, lean_object* v_nanosToAdd_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_Time_PlainTime_addNanoseconds(v_time_509_, v_nanosToAdd_510_);
lean_dec(v_nanosToAdd_510_);
lean_dec_ref(v_time_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds(lean_object* v_time_512_, lean_object* v_nanosToSub_513_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_int_neg(v_nanosToSub_513_);
v___x_515_ = l_Std_Time_PlainTime_addNanoseconds(v_time_512_, v___x_514_);
lean_dec(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds___boxed(lean_object* v_time_516_, lean_object* v_nanosToSub_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Time_PlainTime_subNanoseconds(v_time_516_, v_nanosToSub_517_);
lean_dec(v_nanosToSub_517_);
lean_dec_ref(v_time_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds(lean_object* v_time_519_, lean_object* v_millisToAdd_520_){
_start:
{
lean_object* v___x_521_; lean_object* v_total_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_521_ = l_Std_Time_PlainTime_toMilliseconds(v_time_519_);
v_total_522_ = lean_int_add(v___x_521_, v_millisToAdd_520_);
lean_dec(v___x_521_);
v___x_523_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_524_ = lean_int_mul(v_total_522_, v___x_523_);
lean_dec(v_total_522_);
v___x_525_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_524_);
lean_dec(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds___boxed(lean_object* v_time_526_, lean_object* v_millisToAdd_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_PlainTime_addMilliseconds(v_time_526_, v_millisToAdd_527_);
lean_dec(v_millisToAdd_527_);
lean_dec_ref(v_time_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds(lean_object* v_time_529_, lean_object* v_millisToSub_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_int_neg(v_millisToSub_530_);
v___x_532_ = l_Std_Time_PlainTime_addMilliseconds(v_time_529_, v___x_531_);
lean_dec(v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds___boxed(lean_object* v_time_533_, lean_object* v_millisToSub_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_Time_PlainTime_subMilliseconds(v_time_533_, v_millisToSub_534_);
lean_dec(v_millisToSub_534_);
lean_dec_ref(v_time_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withSeconds(lean_object* v_pt_536_, lean_object* v_second_537_){
_start:
{
lean_object* v_hour_538_; lean_object* v_minute_539_; lean_object* v_nanosecond_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
v_hour_538_ = lean_ctor_get(v_pt_536_, 0);
v_minute_539_ = lean_ctor_get(v_pt_536_, 1);
v_nanosecond_540_ = lean_ctor_get(v_pt_536_, 3);
v_isSharedCheck_547_ = !lean_is_exclusive(v_pt_536_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v_pt_536_, 2);
lean_dec(v_unused_548_);
v___x_542_ = v_pt_536_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_nanosecond_540_);
lean_inc(v_minute_539_);
lean_inc(v_hour_538_);
lean_dec(v_pt_536_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 2, v_second_537_);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_hour_538_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_minute_539_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_second_537_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_nanosecond_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMinutes(lean_object* v_pt_549_, lean_object* v_minute_550_){
_start:
{
lean_object* v_hour_551_; lean_object* v_second_552_; lean_object* v_nanosecond_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_hour_551_ = lean_ctor_get(v_pt_549_, 0);
v_second_552_ = lean_ctor_get(v_pt_549_, 2);
v_nanosecond_553_ = lean_ctor_get(v_pt_549_, 3);
v_isSharedCheck_560_ = !lean_is_exclusive(v_pt_549_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_pt_549_, 1);
lean_dec(v_unused_561_);
v___x_555_ = v_pt_549_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_nanosecond_553_);
lean_inc(v_second_552_);
lean_inc(v_hour_551_);
lean_dec(v_pt_549_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 1, v_minute_550_);
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_hour_551_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_minute_550_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_second_552_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_nanosecond_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds(lean_object* v_pt_562_, lean_object* v_millis_563_){
_start:
{
lean_object* v_hour_564_; lean_object* v_minute_565_; lean_object* v_second_566_; lean_object* v_nanosecond_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_579_; 
v_hour_564_ = lean_ctor_get(v_pt_562_, 0);
v_minute_565_ = lean_ctor_get(v_pt_562_, 1);
v_second_566_ = lean_ctor_get(v_pt_562_, 2);
v_nanosecond_567_ = lean_ctor_get(v_pt_562_, 3);
v_isSharedCheck_579_ = !lean_is_exclusive(v_pt_562_);
if (v_isSharedCheck_579_ == 0)
{
v___x_569_ = v_pt_562_;
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_nanosecond_567_);
lean_inc(v_second_566_);
lean_inc(v_minute_565_);
lean_inc(v_hour_564_);
lean_dec(v_pt_562_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_571_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__2, &l_Std_Time_PlainTime_toMilliseconds___closed__2_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__2);
v___x_572_ = lean_int_emod(v_nanosecond_567_, v___x_571_);
lean_dec(v_nanosecond_567_);
v___x_573_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_574_ = lean_int_mul(v_millis_563_, v___x_573_);
v___x_575_ = lean_int_add(v___x_574_, v___x_572_);
lean_dec(v___x_572_);
lean_dec(v___x_574_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 3, v___x_575_);
v___x_577_ = v___x_569_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_hour_564_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_minute_565_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_second_566_);
lean_ctor_set(v_reuseFailAlloc_578_, 3, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds___boxed(lean_object* v_pt_580_, lean_object* v_millis_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Std_Time_PlainTime_withMilliseconds(v_pt_580_, v_millis_581_);
lean_dec(v_millis_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withNanoseconds(lean_object* v_pt_583_, lean_object* v_nano_584_){
_start:
{
lean_object* v_hour_585_; lean_object* v_minute_586_; lean_object* v_second_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_hour_585_ = lean_ctor_get(v_pt_583_, 0);
v_minute_586_ = lean_ctor_get(v_pt_583_, 1);
v_second_587_ = lean_ctor_get(v_pt_583_, 2);
v_isSharedCheck_594_ = !lean_is_exclusive(v_pt_583_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v_pt_583_, 3);
lean_dec(v_unused_595_);
v___x_589_ = v_pt_583_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_second_587_);
lean_inc(v_minute_586_);
lean_inc(v_hour_585_);
lean_dec(v_pt_583_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 3, v_nano_584_);
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_hour_585_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_minute_586_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v_second_587_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_nano_584_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withHours(lean_object* v_pt_596_, lean_object* v_hour_597_){
_start:
{
lean_object* v_minute_598_; lean_object* v_second_599_; lean_object* v_nanosecond_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_minute_598_ = lean_ctor_get(v_pt_596_, 1);
v_second_599_ = lean_ctor_get(v_pt_596_, 2);
v_nanosecond_600_ = lean_ctor_get(v_pt_596_, 3);
v_isSharedCheck_607_ = !lean_is_exclusive(v_pt_596_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v_pt_596_, 0);
lean_dec(v_unused_608_);
v___x_602_ = v_pt_596_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_nanosecond_600_);
lean_inc(v_second_599_);
lean_inc(v_minute_598_);
lean_dec(v_pt_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_hour_597_);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_hour_597_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_minute_598_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_second_599_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_nanosecond_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond(lean_object* v_pt_609_){
_start:
{
lean_object* v_nanosecond_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_nanosecond_610_ = lean_ctor_get(v_pt_609_, 3);
v___x_611_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_612_ = lean_int_ediv(v_nanosecond_610_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond___boxed(lean_object* v_pt_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Time_PlainTime_millisecond(v_pt_613_);
lean_dec_ref(v_pt_613_);
return v_res_614_;
}
}
lean_object* runtime_initialize_Std_Time_Time_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Time_PlainTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
