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
lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
extern lean_object* l_Std_Time_Nanosecond_instAddOffset;
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
extern lean_object* l_Std_Time_Nanosecond_instOrdOrdinal;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Second_instOrdOrdinal(uint8_t);
lean_object* l_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_Std_Time_Millisecond_instAddOffset;
lean_object* lean_int_div(lean_object*, lean_object*);
extern lean_object* l_Std_Time_Minute_instOrdOrdinal;
extern lean_object* l_Std_Time_Hour_instOrdOrdinal;
extern lean_object* l_Std_Time_Minute_instAddOffset;
extern lean_object* l_Std_Time_Second_instAddOffset;
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
static lean_once_cell_t l_Std_Time_instOrdPlainTime___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainTime___closed__4;
static lean_once_cell_t l_Std_Time_instOrdPlainTime___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainTime___closed__5;
static lean_once_cell_t l_Std_Time_instOrdPlainTime___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainTime___closed__6;
static lean_once_cell_t l_Std_Time_instOrdPlainTime___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainTime___closed__7;
static lean_once_cell_t l_Std_Time_instOrdPlainTime___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainTime___closed__8;
static lean_once_cell_t l_Std_Time_instOrdPlainTime___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainTime___closed__9;
static lean_once_cell_t l_Std_Time_instOrdPlainTime___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainTime___closed__10;
static lean_once_cell_t l_Std_Time_instOrdPlainTime___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdPlainTime___closed__11;
LEAN_EXPORT lean_object* l_Std_Time_instOrdPlainTime;
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
static lean_once_cell_t l_Std_Time_PlainTime_toSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toSeconds___closed__0;
static lean_once_cell_t l_Std_Time_PlainTime_toSeconds___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_toSeconds___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes(lean_object*);
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
static const lean_closure_object l_Std_Time_PlainTime_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_addNanoseconds, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
v___x_54_ = l_Std_Time_Internal_Bounded_instRepr___lam__0(v_hour_46_, v___x_53_);
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
v___x_67_ = l_Std_Time_Internal_Bounded_instRepr___lam__0(v_minute_47_, v___x_53_);
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
v___x_87_ = l_Std_Time_Internal_Bounded_instRepr___lam__0(v_nanosecond_49_, v___x_53_);
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
static lean_object* _init_l_Std_Time_instOrdPlainTime___closed__4(void){
_start:
{
lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___f_219_ = ((lean_object*)(l_Std_Time_instOrdPlainTime___closed__0));
v___x_220_ = l_Std_Time_Hour_instOrdOrdinal;
v___x_221_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_221_, 0, lean_box(0));
lean_closure_set(v___x_221_, 1, lean_box(0));
lean_closure_set(v___x_221_, 2, v___x_220_);
lean_closure_set(v___x_221_, 3, v___f_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainTime___closed__5(void){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___f_222_ = ((lean_object*)(l_Std_Time_instOrdPlainTime___closed__1));
v___x_223_ = l_Std_Time_Minute_instOrdOrdinal;
v___x_224_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_224_, 0, lean_box(0));
lean_closure_set(v___x_224_, 1, lean_box(0));
lean_closure_set(v___x_224_, 2, v___x_223_);
lean_closure_set(v___x_224_, 3, v___f_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainTime___closed__6(void){
_start:
{
uint8_t v___x_225_; lean_object* v___x_226_; 
v___x_225_ = 1;
v___x_226_ = l_Std_Time_Second_instOrdOrdinal(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainTime___closed__7(void){
_start:
{
lean_object* v___f_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___f_227_ = ((lean_object*)(l_Std_Time_instOrdPlainTime___closed__2));
v___x_228_ = lean_obj_once(&l_Std_Time_instOrdPlainTime___closed__6, &l_Std_Time_instOrdPlainTime___closed__6_once, _init_l_Std_Time_instOrdPlainTime___closed__6);
v___x_229_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, lean_box(0));
lean_closure_set(v___x_229_, 2, v___x_228_);
lean_closure_set(v___x_229_, 3, v___f_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainTime___closed__8(void){
_start:
{
lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___f_230_ = ((lean_object*)(l_Std_Time_instOrdPlainTime___closed__3));
v___x_231_ = l_Std_Time_Nanosecond_instOrdOrdinal;
v___x_232_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_232_, 0, lean_box(0));
lean_closure_set(v___x_232_, 1, lean_box(0));
lean_closure_set(v___x_232_, 2, v___x_231_);
lean_closure_set(v___x_232_, 3, v___f_230_);
return v___x_232_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainTime___closed__9(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l_Std_Time_instOrdPlainTime___closed__8, &l_Std_Time_instOrdPlainTime___closed__8_once, _init_l_Std_Time_instOrdPlainTime___closed__8);
v___x_234_ = lean_obj_once(&l_Std_Time_instOrdPlainTime___closed__7, &l_Std_Time_instOrdPlainTime___closed__7_once, _init_l_Std_Time_instOrdPlainTime___closed__7);
v___x_235_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_235_, 0, lean_box(0));
lean_closure_set(v___x_235_, 1, lean_box(0));
lean_closure_set(v___x_235_, 2, v___x_234_);
lean_closure_set(v___x_235_, 3, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainTime___closed__10(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_obj_once(&l_Std_Time_instOrdPlainTime___closed__9, &l_Std_Time_instOrdPlainTime___closed__9_once, _init_l_Std_Time_instOrdPlainTime___closed__9);
v___x_237_ = lean_obj_once(&l_Std_Time_instOrdPlainTime___closed__5, &l_Std_Time_instOrdPlainTime___closed__5_once, _init_l_Std_Time_instOrdPlainTime___closed__5);
v___x_238_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_238_, 0, lean_box(0));
lean_closure_set(v___x_238_, 1, lean_box(0));
lean_closure_set(v___x_238_, 2, v___x_237_);
lean_closure_set(v___x_238_, 3, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainTime___closed__11(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_Std_Time_instOrdPlainTime___closed__10, &l_Std_Time_instOrdPlainTime___closed__10_once, _init_l_Std_Time_instOrdPlainTime___closed__10);
v___x_240_ = lean_obj_once(&l_Std_Time_instOrdPlainTime___closed__4, &l_Std_Time_instOrdPlainTime___closed__4_once, _init_l_Std_Time_instOrdPlainTime___closed__4);
v___x_241_ = lean_alloc_closure((void*)(l_compareLex___boxed), 6, 4);
lean_closure_set(v___x_241_, 0, lean_box(0));
lean_closure_set(v___x_241_, 1, lean_box(0));
lean_closure_set(v___x_241_, 2, v___x_240_);
lean_closure_set(v___x_241_, 3, v___x_239_);
return v___x_241_;
}
}
static lean_object* _init_l_Std_Time_instOrdPlainTime(void){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&l_Std_Time_instOrdPlainTime___closed__11, &l_Std_Time_instOrdPlainTime___closed__11_once, _init_l_Std_Time_instOrdPlainTime___closed__11);
return v___x_242_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__0(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(23u);
v___x_244_ = lean_nat_to_int(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__1(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_245_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__0, &l_Std_Time_PlainTime_midnight___closed__0_once, _init_l_Std_Time_PlainTime_midnight___closed__0);
v___x_246_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_247_ = lean_int_add(v___x_246_, v___x_245_);
return v___x_247_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_249_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__1, &l_Std_Time_PlainTime_midnight___closed__1_once, _init_l_Std_Time_PlainTime_midnight___closed__1);
v___x_250_ = lean_int_sub(v___x_249_, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__3(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_range_253_; 
v___x_251_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_252_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__2, &l_Std_Time_PlainTime_midnight___closed__2_once, _init_l_Std_Time_PlainTime_midnight___closed__2);
v_range_253_ = lean_int_add(v___x_252_, v___x_251_);
return v_range_253_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__4(void){
_start:
{
lean_object* v_range_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_range_254_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_255_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_256_ = lean_int_emod(v___x_255_, v_range_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__5(void){
_start:
{
lean_object* v_range_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_range_257_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_258_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__4, &l_Std_Time_PlainTime_midnight___closed__4_once, _init_l_Std_Time_PlainTime_midnight___closed__4);
v___x_259_ = lean_int_add(v___x_258_, v_range_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__6(void){
_start:
{
lean_object* v_range_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_range_260_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__3, &l_Std_Time_PlainTime_midnight___closed__3_once, _init_l_Std_Time_PlainTime_midnight___closed__3);
v___x_261_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__5, &l_Std_Time_PlainTime_midnight___closed__5_once, _init_l_Std_Time_PlainTime_midnight___closed__5);
v___x_262_ = lean_int_emod(v___x_261_, v_range_260_);
return v___x_262_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__7(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_264_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__6, &l_Std_Time_PlainTime_midnight___closed__6_once, _init_l_Std_Time_PlainTime_midnight___closed__6);
v___x_265_ = lean_int_add(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__8(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_unsigned_to_nat(59u);
v___x_267_ = lean_nat_to_int(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__9(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__8, &l_Std_Time_PlainTime_midnight___closed__8_once, _init_l_Std_Time_PlainTime_midnight___closed__8);
v___x_269_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_270_ = lean_int_add(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__10(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_272_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__9, &l_Std_Time_PlainTime_midnight___closed__9_once, _init_l_Std_Time_PlainTime_midnight___closed__9);
v___x_273_ = lean_int_sub(v___x_272_, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__11(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v_range_276_; 
v___x_274_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__3, &l_Std_Time_instInhabitedPlainTime___closed__3_once, _init_l_Std_Time_instInhabitedPlainTime___closed__3);
v___x_275_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__10, &l_Std_Time_PlainTime_midnight___closed__10_once, _init_l_Std_Time_PlainTime_midnight___closed__10);
v_range_276_ = lean_int_add(v___x_275_, v___x_274_);
return v_range_276_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__12(void){
_start:
{
lean_object* v_range_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_range_277_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_278_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__5, &l_Std_Time_instInhabitedPlainTime___closed__5_once, _init_l_Std_Time_instInhabitedPlainTime___closed__5);
v___x_279_ = lean_int_emod(v___x_278_, v_range_277_);
return v___x_279_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__13(void){
_start:
{
lean_object* v_range_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_range_280_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_281_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__12, &l_Std_Time_PlainTime_midnight___closed__12_once, _init_l_Std_Time_PlainTime_midnight___closed__12);
v___x_282_ = lean_int_add(v___x_281_, v_range_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__14(void){
_start:
{
lean_object* v_range_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_range_283_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__11, &l_Std_Time_PlainTime_midnight___closed__11_once, _init_l_Std_Time_PlainTime_midnight___closed__11);
v___x_284_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__13, &l_Std_Time_PlainTime_midnight___closed__13_once, _init_l_Std_Time_PlainTime_midnight___closed__13);
v___x_285_ = lean_int_emod(v___x_284_, v_range_283_);
return v___x_285_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__15(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_obj_once(&l_Std_Time_instReprPlainTime_repr___redArg___closed__23, &l_Std_Time_instReprPlainTime_repr___redArg___closed__23_once, _init_l_Std_Time_instReprPlainTime_repr___redArg___closed__23);
v___x_287_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__14, &l_Std_Time_PlainTime_midnight___closed__14_once, _init_l_Std_Time_PlainTime_midnight___closed__14);
v___x_288_ = lean_int_add(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__16(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_unsigned_to_nat(1000000000u);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_nat_mod(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__17(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__16, &l_Std_Time_PlainTime_midnight___closed__16_once, _init_l_Std_Time_PlainTime_midnight___closed__16);
v___x_293_ = lean_nat_to_int(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight___closed__18(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_294_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__17, &l_Std_Time_PlainTime_midnight___closed__17_once, _init_l_Std_Time_PlainTime_midnight___closed__17);
v___x_295_ = lean_obj_once(&l_Std_Time_instInhabitedPlainTime___closed__18, &l_Std_Time_instInhabitedPlainTime___closed__18_once, _init_l_Std_Time_instInhabitedPlainTime___closed__18);
v___x_296_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__15, &l_Std_Time_PlainTime_midnight___closed__15_once, _init_l_Std_Time_PlainTime_midnight___closed__15);
v___x_297_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__7, &l_Std_Time_PlainTime_midnight___closed__7_once, _init_l_Std_Time_PlainTime_midnight___closed__7);
v___x_298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
lean_ctor_set(v___x_298_, 2, v___x_295_);
lean_ctor_set(v___x_298_, 3, v___x_294_);
return v___x_298_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_midnight(void){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__18, &l_Std_Time_PlainTime_midnight___closed__18_once, _init_l_Std_Time_PlainTime_midnight___closed__18);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSecondsNano(lean_object* v_hour_300_, lean_object* v_minute_301_, lean_object* v_second_302_, lean_object* v_nano_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_304_, 0, v_hour_300_);
lean_ctor_set(v___x_304_, 1, v_minute_301_);
lean_ctor_set(v___x_304_, 2, v_second_302_);
lean_ctor_set(v___x_304_, 3, v_nano_303_);
return v___x_304_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l_Std_Time_PlainTime_midnight___closed__16, &l_Std_Time_PlainTime_midnight___closed__16_once, _init_l_Std_Time_PlainTime_midnight___closed__16);
v___x_306_ = lean_nat_to_int(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_ofHourMinuteSeconds(lean_object* v_hour_307_, lean_object* v_minute_308_, lean_object* v_second_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_obj_once(&l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0, &l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0_once, _init_l_Std_Time_PlainTime_ofHourMinuteSeconds___closed__0);
v___x_311_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_311_, 0, v_hour_307_);
lean_ctor_set(v___x_311_, 1, v_minute_308_);
lean_ctor_set(v___x_311_, 2, v_second_309_);
lean_ctor_set(v___x_311_, 3, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__1(lean_object* v_a_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Rat_ofInt(v_a_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(3600000u);
v___x_315_ = lean_nat_to_int(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(60000u);
v___x_317_ = lean_nat_to_int(v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__2(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1000u);
v___x_319_ = lean_nat_to_int(v___x_318_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toMilliseconds___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(1000000u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object* v_time_322_){
_start:
{
lean_object* v_hour_323_; lean_object* v_minute_324_; lean_object* v_second_325_; lean_object* v_nanosecond_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_70__overap_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_88__overap_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_116__overap_339_; lean_object* v___x_340_; 
v_hour_323_ = lean_ctor_get(v_time_322_, 0);
v_minute_324_ = lean_ctor_get(v_time_322_, 1);
v_second_325_ = lean_ctor_get(v_time_322_, 2);
v_nanosecond_326_ = lean_ctor_get(v_time_322_, 3);
v___x_327_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__0, &l_Std_Time_PlainTime_toMilliseconds___closed__0_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__0);
v___x_328_ = lean_int_mul(v_hour_323_, v___x_327_);
v___x_329_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__1, &l_Std_Time_PlainTime_toMilliseconds___closed__1_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__1);
v___x_330_ = lean_int_mul(v_minute_324_, v___x_329_);
v___x_70__overap_331_ = l_Std_Time_Millisecond_instAddOffset;
v___x_332_ = lean_apply_2(v___x_70__overap_331_, v___x_328_, v___x_330_);
v___x_333_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__2, &l_Std_Time_PlainTime_toMilliseconds___closed__2_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__2);
v___x_334_ = lean_int_mul(v_second_325_, v___x_333_);
v___x_88__overap_335_ = l_Std_Time_Millisecond_instAddOffset;
v___x_336_ = lean_apply_2(v___x_88__overap_335_, v___x_332_, v___x_334_);
v___x_337_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_338_ = lean_int_div(v_nanosecond_326_, v___x_337_);
v___x_116__overap_339_ = l_Std_Time_Millisecond_instAddOffset;
v___x_340_ = lean_apply_2(v___x_116__overap_339_, v___x_336_, v___x_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMilliseconds___boxed(lean_object* v_time_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Time_PlainTime_toMilliseconds(v_time_341_);
lean_dec_ref(v_time_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_PlainTime_toMilliseconds_spec__0(lean_object* v_a_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_nat_to_int(v_a_343_);
v___x_345_ = l_Rat_ofInt(v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__0(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_cstr_to_nat("3600000000000");
v___x_347_ = lean_nat_to_int(v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__1(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_cstr_to_nat("60000000000");
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_toNanoseconds___closed__2(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(1000000000u);
v___x_351_ = lean_nat_to_int(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object* v_time_352_){
_start:
{
lean_object* v_hour_353_; lean_object* v_minute_354_; lean_object* v_second_355_; lean_object* v_nanosecond_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_69__overap_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_87__overap_365_; lean_object* v___x_366_; lean_object* v___x_97__overap_367_; lean_object* v___x_368_; 
v_hour_353_ = lean_ctor_get(v_time_352_, 0);
lean_inc(v_hour_353_);
v_minute_354_ = lean_ctor_get(v_time_352_, 1);
lean_inc(v_minute_354_);
v_second_355_ = lean_ctor_get(v_time_352_, 2);
lean_inc(v_second_355_);
v_nanosecond_356_ = lean_ctor_get(v_time_352_, 3);
lean_inc(v_nanosecond_356_);
lean_dec_ref(v_time_352_);
v___x_357_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_358_ = lean_int_mul(v_hour_353_, v___x_357_);
lean_dec(v_hour_353_);
v___x_359_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_360_ = lean_int_mul(v_minute_354_, v___x_359_);
lean_dec(v_minute_354_);
v___x_69__overap_361_ = l_Std_Time_Nanosecond_instAddOffset;
v___x_362_ = lean_apply_2(v___x_69__overap_361_, v___x_358_, v___x_360_);
v___x_363_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_364_ = lean_int_mul(v_second_355_, v___x_363_);
lean_dec(v_second_355_);
v___x_87__overap_365_ = l_Std_Time_Nanosecond_instAddOffset;
v___x_366_ = lean_apply_2(v___x_87__overap_365_, v___x_362_, v___x_364_);
v___x_97__overap_367_ = l_Std_Time_Nanosecond_instAddOffset;
v___x_368_ = lean_apply_2(v___x_97__overap_367_, v___x_366_, v_nanosecond_356_);
return v___x_368_;
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
lean_object* v_hour_374_; lean_object* v_minute_375_; lean_object* v_second_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_57__overap_381_; lean_object* v___x_382_; lean_object* v___x_64__overap_383_; lean_object* v___x_384_; 
v_hour_374_ = lean_ctor_get(v_time_373_, 0);
lean_inc(v_hour_374_);
v_minute_375_ = lean_ctor_get(v_time_373_, 1);
lean_inc(v_minute_375_);
v_second_376_ = lean_ctor_get(v_time_373_, 2);
lean_inc(v_second_376_);
lean_dec_ref(v_time_373_);
v___x_377_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__0, &l_Std_Time_PlainTime_toSeconds___closed__0_once, _init_l_Std_Time_PlainTime_toSeconds___closed__0);
v___x_378_ = lean_int_mul(v_hour_374_, v___x_377_);
lean_dec(v_hour_374_);
v___x_379_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v___x_380_ = lean_int_mul(v_minute_375_, v___x_379_);
lean_dec(v_minute_375_);
v___x_57__overap_381_ = l_Std_Time_Second_instAddOffset;
v___x_382_ = lean_apply_2(v___x_57__overap_381_, v___x_378_, v___x_380_);
v___x_64__overap_383_ = l_Std_Time_Second_instAddOffset;
v___x_384_ = lean_apply_2(v___x_64__overap_383_, v___x_382_, v_second_376_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toMinutes(lean_object* v_time_385_){
_start:
{
lean_object* v_hour_386_; lean_object* v_minute_387_; lean_object* v_second_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_44__overap_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_64__overap_394_; lean_object* v___x_395_; 
v_hour_386_ = lean_ctor_get(v_time_385_, 0);
lean_inc(v_hour_386_);
v_minute_387_ = lean_ctor_get(v_time_385_, 1);
lean_inc(v_minute_387_);
v_second_388_ = lean_ctor_get(v_time_385_, 2);
lean_inc(v_second_388_);
lean_dec_ref(v_time_385_);
v___x_389_ = lean_obj_once(&l_Std_Time_PlainTime_toSeconds___closed__1, &l_Std_Time_PlainTime_toSeconds___closed__1_once, _init_l_Std_Time_PlainTime_toSeconds___closed__1);
v___x_390_ = lean_int_mul(v_hour_386_, v___x_389_);
lean_dec(v_hour_386_);
v___x_44__overap_391_ = l_Std_Time_Minute_instAddOffset;
v___x_392_ = lean_apply_2(v___x_44__overap_391_, v___x_390_, v_minute_387_);
v___x_393_ = lean_int_div(v_second_388_, v___x_389_);
lean_dec(v_second_388_);
v___x_64__overap_394_ = l_Std_Time_Minute_instAddOffset;
v___x_395_ = lean_apply_2(v___x_64__overap_394_, v___x_392_, v___x_393_);
return v___x_395_;
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
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_totalSeconds_overap_446_; lean_object* v_totalSeconds_447_; lean_object* v___x_448_; 
v___x_443_ = l_Std_Time_PlainTime_toNanoseconds(v_time_441_);
v___x_444_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_445_ = lean_int_mul(v_secondsToAdd_442_, v___x_444_);
v_totalSeconds_overap_446_ = l_Std_Time_Nanosecond_instAddOffset;
v_totalSeconds_447_ = lean_apply_2(v_totalSeconds_overap_446_, v___x_443_, v___x_445_);
v___x_448_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_447_);
lean_dec(v_totalSeconds_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addSeconds___boxed(lean_object* v_time_449_, lean_object* v_secondsToAdd_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_Time_PlainTime_addSeconds(v_time_449_, v_secondsToAdd_450_);
lean_dec(v_secondsToAdd_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds(lean_object* v_time_452_, lean_object* v_secondsToSub_453_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v_totalSeconds_overap_458_; lean_object* v_totalSeconds_459_; lean_object* v___x_460_; 
v___x_454_ = lean_int_neg(v_secondsToSub_453_);
v___x_455_ = l_Std_Time_PlainTime_toNanoseconds(v_time_452_);
v___x_456_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__2, &l_Std_Time_PlainTime_toNanoseconds___closed__2_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__2);
v___x_457_ = lean_int_mul(v___x_454_, v___x_456_);
lean_dec(v___x_454_);
v_totalSeconds_overap_458_ = l_Std_Time_Nanosecond_instAddOffset;
v_totalSeconds_459_ = lean_apply_2(v_totalSeconds_overap_458_, v___x_455_, v___x_457_);
v___x_460_ = l_Std_Time_PlainTime_ofNanoseconds(v_totalSeconds_459_);
lean_dec(v_totalSeconds_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subSeconds___boxed(lean_object* v_time_461_, lean_object* v_secondsToSub_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_Time_PlainTime_subSeconds(v_time_461_, v_secondsToSub_462_);
lean_dec(v_secondsToSub_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes(lean_object* v_time_464_, lean_object* v_minutesToAdd_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v_total_overap_469_; lean_object* v_total_470_; lean_object* v___x_471_; 
v___x_466_ = l_Std_Time_PlainTime_toNanoseconds(v_time_464_);
v___x_467_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_468_ = lean_int_mul(v_minutesToAdd_465_, v___x_467_);
v_total_overap_469_ = l_Std_Time_Nanosecond_instAddOffset;
v_total_470_ = lean_apply_2(v_total_overap_469_, v___x_466_, v___x_468_);
v___x_471_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_470_);
lean_dec(v_total_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMinutes___boxed(lean_object* v_time_472_, lean_object* v_minutesToAdd_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Time_PlainTime_addMinutes(v_time_472_, v_minutesToAdd_473_);
lean_dec(v_minutesToAdd_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes(lean_object* v_time_475_, lean_object* v_minutesToSub_476_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v_total_overap_481_; lean_object* v_total_482_; lean_object* v___x_483_; 
v___x_477_ = lean_int_neg(v_minutesToSub_476_);
v___x_478_ = l_Std_Time_PlainTime_toNanoseconds(v_time_475_);
v___x_479_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__1, &l_Std_Time_PlainTime_toNanoseconds___closed__1_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__1);
v___x_480_ = lean_int_mul(v___x_477_, v___x_479_);
lean_dec(v___x_477_);
v_total_overap_481_ = l_Std_Time_Nanosecond_instAddOffset;
v_total_482_ = lean_apply_2(v_total_overap_481_, v___x_478_, v___x_480_);
v___x_483_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_482_);
lean_dec(v_total_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMinutes___boxed(lean_object* v_time_484_, lean_object* v_minutesToSub_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Time_PlainTime_subMinutes(v_time_484_, v_minutesToSub_485_);
lean_dec(v_minutesToSub_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours(lean_object* v_time_487_, lean_object* v_hoursToAdd_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_total_overap_492_; lean_object* v_total_493_; lean_object* v___x_494_; 
v___x_489_ = l_Std_Time_PlainTime_toNanoseconds(v_time_487_);
v___x_490_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_491_ = lean_int_mul(v_hoursToAdd_488_, v___x_490_);
v_total_overap_492_ = l_Std_Time_Nanosecond_instAddOffset;
v_total_493_ = lean_apply_2(v_total_overap_492_, v___x_489_, v___x_491_);
v___x_494_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_493_);
lean_dec(v_total_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addHours___boxed(lean_object* v_time_495_, lean_object* v_hoursToAdd_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Time_PlainTime_addHours(v_time_495_, v_hoursToAdd_496_);
lean_dec(v_hoursToAdd_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours(lean_object* v_time_498_, lean_object* v_hoursToSub_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_total_overap_504_; lean_object* v_total_505_; lean_object* v___x_506_; 
v___x_500_ = lean_int_neg(v_hoursToSub_499_);
v___x_501_ = l_Std_Time_PlainTime_toNanoseconds(v_time_498_);
v___x_502_ = lean_obj_once(&l_Std_Time_PlainTime_toNanoseconds___closed__0, &l_Std_Time_PlainTime_toNanoseconds___closed__0_once, _init_l_Std_Time_PlainTime_toNanoseconds___closed__0);
v___x_503_ = lean_int_mul(v___x_500_, v___x_502_);
lean_dec(v___x_500_);
v_total_overap_504_ = l_Std_Time_Nanosecond_instAddOffset;
v_total_505_ = lean_apply_2(v_total_overap_504_, v___x_501_, v___x_503_);
v___x_506_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_505_);
lean_dec(v_total_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subHours___boxed(lean_object* v_time_507_, lean_object* v_hoursToSub_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Time_PlainTime_subHours(v_time_507_, v_hoursToSub_508_);
lean_dec(v_hoursToSub_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addNanoseconds(lean_object* v_time_510_, lean_object* v_nanosToAdd_511_){
_start:
{
lean_object* v___x_512_; lean_object* v_total_overap_513_; lean_object* v_total_514_; lean_object* v___x_515_; 
v___x_512_ = l_Std_Time_PlainTime_toNanoseconds(v_time_510_);
v_total_overap_513_ = l_Std_Time_Nanosecond_instAddOffset;
v_total_514_ = lean_apply_2(v_total_overap_513_, v___x_512_, v_nanosToAdd_511_);
v___x_515_ = l_Std_Time_PlainTime_ofNanoseconds(v_total_514_);
lean_dec(v_total_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds(lean_object* v_time_516_, lean_object* v_nanosToSub_517_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_int_neg(v_nanosToSub_517_);
v___x_519_ = l_Std_Time_PlainTime_addNanoseconds(v_time_516_, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subNanoseconds___boxed(lean_object* v_time_520_, lean_object* v_nanosToSub_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Time_PlainTime_subNanoseconds(v_time_520_, v_nanosToSub_521_);
lean_dec(v_nanosToSub_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds(lean_object* v_time_523_, lean_object* v_millisToAdd_524_){
_start:
{
lean_object* v___x_525_; lean_object* v_total_overap_526_; lean_object* v_total_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_525_ = l_Std_Time_PlainTime_toMilliseconds(v_time_523_);
v_total_overap_526_ = l_Std_Time_Millisecond_instAddOffset;
v_total_527_ = lean_apply_2(v_total_overap_526_, v___x_525_, v_millisToAdd_524_);
v___x_528_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_529_ = lean_int_mul(v_total_527_, v___x_528_);
lean_dec(v_total_527_);
v___x_530_ = l_Std_Time_PlainTime_ofNanoseconds(v___x_529_);
lean_dec(v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_addMilliseconds___boxed(lean_object* v_time_531_, lean_object* v_millisToAdd_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_Time_PlainTime_addMilliseconds(v_time_531_, v_millisToAdd_532_);
lean_dec_ref(v_time_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds(lean_object* v_time_534_, lean_object* v_millisToSub_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_int_neg(v_millisToSub_535_);
v___x_537_ = l_Std_Time_PlainTime_addMilliseconds(v_time_534_, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_subMilliseconds___boxed(lean_object* v_time_538_, lean_object* v_millisToSub_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Time_PlainTime_subMilliseconds(v_time_538_, v_millisToSub_539_);
lean_dec(v_millisToSub_539_);
lean_dec_ref(v_time_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withSeconds(lean_object* v_pt_541_, lean_object* v_second_542_){
_start:
{
lean_object* v_hour_543_; lean_object* v_minute_544_; lean_object* v_nanosecond_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_hour_543_ = lean_ctor_get(v_pt_541_, 0);
v_minute_544_ = lean_ctor_get(v_pt_541_, 1);
v_nanosecond_545_ = lean_ctor_get(v_pt_541_, 3);
v_isSharedCheck_552_ = !lean_is_exclusive(v_pt_541_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_pt_541_, 2);
lean_dec(v_unused_553_);
v___x_547_ = v_pt_541_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_nanosecond_545_);
lean_inc(v_minute_544_);
lean_inc(v_hour_543_);
lean_dec(v_pt_541_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 2, v_second_542_);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_hour_543_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_minute_544_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_second_542_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_nanosecond_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMinutes(lean_object* v_pt_554_, lean_object* v_minute_555_){
_start:
{
lean_object* v_hour_556_; lean_object* v_second_557_; lean_object* v_nanosecond_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
v_hour_556_ = lean_ctor_get(v_pt_554_, 0);
v_second_557_ = lean_ctor_get(v_pt_554_, 2);
v_nanosecond_558_ = lean_ctor_get(v_pt_554_, 3);
v_isSharedCheck_565_ = !lean_is_exclusive(v_pt_554_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v_pt_554_, 1);
lean_dec(v_unused_566_);
v___x_560_ = v_pt_554_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_nanosecond_558_);
lean_inc(v_second_557_);
lean_inc(v_hour_556_);
lean_dec(v_pt_554_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_minute_555_);
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_hour_556_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_minute_555_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_second_557_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_nanosecond_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds(lean_object* v_pt_567_, lean_object* v_millis_568_){
_start:
{
lean_object* v_hour_569_; lean_object* v_minute_570_; lean_object* v_second_571_; lean_object* v_nanosecond_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_584_; 
v_hour_569_ = lean_ctor_get(v_pt_567_, 0);
v_minute_570_ = lean_ctor_get(v_pt_567_, 1);
v_second_571_ = lean_ctor_get(v_pt_567_, 2);
v_nanosecond_572_ = lean_ctor_get(v_pt_567_, 3);
v_isSharedCheck_584_ = !lean_is_exclusive(v_pt_567_);
if (v_isSharedCheck_584_ == 0)
{
v___x_574_ = v_pt_567_;
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_nanosecond_572_);
lean_inc(v_second_571_);
lean_inc(v_minute_570_);
lean_inc(v_hour_569_);
lean_dec(v_pt_567_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_584_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_576_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__2, &l_Std_Time_PlainTime_toMilliseconds___closed__2_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__2);
v___x_577_ = lean_int_emod(v_nanosecond_572_, v___x_576_);
lean_dec(v_nanosecond_572_);
v___x_578_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_579_ = lean_int_mul(v_millis_568_, v___x_578_);
v___x_580_ = lean_int_add(v___x_579_, v___x_577_);
lean_dec(v___x_577_);
lean_dec(v___x_579_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 3, v___x_580_);
v___x_582_ = v___x_574_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_hour_569_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_minute_570_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_second_571_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withMilliseconds___boxed(lean_object* v_pt_585_, lean_object* v_millis_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_Time_PlainTime_withMilliseconds(v_pt_585_, v_millis_586_);
lean_dec(v_millis_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withNanoseconds(lean_object* v_pt_588_, lean_object* v_nano_589_){
_start:
{
lean_object* v_hour_590_; lean_object* v_minute_591_; lean_object* v_second_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_hour_590_ = lean_ctor_get(v_pt_588_, 0);
v_minute_591_ = lean_ctor_get(v_pt_588_, 1);
v_second_592_ = lean_ctor_get(v_pt_588_, 2);
v_isSharedCheck_599_ = !lean_is_exclusive(v_pt_588_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_pt_588_, 3);
lean_dec(v_unused_600_);
v___x_594_ = v_pt_588_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_second_592_);
lean_inc(v_minute_591_);
lean_inc(v_hour_590_);
lean_dec(v_pt_588_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 3, v_nano_589_);
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_hour_590_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_minute_591_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_second_592_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_nano_589_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_withHours(lean_object* v_pt_601_, lean_object* v_hour_602_){
_start:
{
lean_object* v_minute_603_; lean_object* v_second_604_; lean_object* v_nanosecond_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_minute_603_ = lean_ctor_get(v_pt_601_, 1);
v_second_604_ = lean_ctor_get(v_pt_601_, 2);
v_nanosecond_605_ = lean_ctor_get(v_pt_601_, 3);
v_isSharedCheck_612_ = !lean_is_exclusive(v_pt_601_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v_pt_601_, 0);
lean_dec(v_unused_613_);
v___x_607_ = v_pt_601_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_nanosecond_605_);
lean_inc(v_second_604_);
lean_inc(v_minute_603_);
lean_dec(v_pt_601_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_hour_602_);
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_hour_602_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_minute_603_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_second_604_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_nanosecond_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond(lean_object* v_pt_614_){
_start:
{
lean_object* v_nanosecond_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_nanosecond_615_ = lean_ctor_get(v_pt_614_, 3);
v___x_616_ = lean_obj_once(&l_Std_Time_PlainTime_toMilliseconds___closed__3, &l_Std_Time_PlainTime_toMilliseconds___closed__3_once, _init_l_Std_Time_PlainTime_toMilliseconds___closed__3);
v___x_617_ = lean_int_ediv(v_nanosecond_615_, v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_millisecond___boxed(lean_object* v_pt_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_Time_PlainTime_millisecond(v_pt_618_);
lean_dec_ref(v_pt_618_);
return v_res_619_;
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
l_Std_Time_instOrdPlainTime = _init_l_Std_Time_instOrdPlainTime();
lean_mark_persistent(l_Std_Time_instOrdPlainTime);
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
