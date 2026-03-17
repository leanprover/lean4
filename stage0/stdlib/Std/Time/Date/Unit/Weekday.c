// Lean compiler output
// Module: Std.Time.Date.Unit.Weekday
// Imports: public import Std.Time.Date.Unit.Day
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
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(lean_object*);
lean_object* l_instOrdInt___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_monday_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_monday_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_monday_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_monday_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_tuesday_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_tuesday_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_tuesday_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_tuesday_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_wednesday_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_wednesday_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_wednesday_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_wednesday_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_thursday_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_thursday_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_thursday_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_thursday_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_friday_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_friday_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_friday_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_friday_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_saturday_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_saturday_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_saturday_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_saturday_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_sunday_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_sunday_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_sunday_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_sunday_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instReprWeekday_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.Weekday.monday"};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__0 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprWeekday_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWeekday_repr___closed__0_value)}};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__1 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__1_value;
static const lean_string_object l_Std_Time_instReprWeekday_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.Time.Weekday.tuesday"};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__2 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprWeekday_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWeekday_repr___closed__2_value)}};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__3 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__3_value;
static const lean_string_object l_Std_Time_instReprWeekday_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Time.Weekday.wednesday"};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__4 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprWeekday_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWeekday_repr___closed__4_value)}};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__5 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__5_value;
static const lean_string_object l_Std_Time_instReprWeekday_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Std.Time.Weekday.thursday"};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__6 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprWeekday_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWeekday_repr___closed__6_value)}};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__7 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__7_value;
static const lean_string_object l_Std_Time_instReprWeekday_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.Weekday.friday"};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__8 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__8_value;
static const lean_ctor_object l_Std_Time_instReprWeekday_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWeekday_repr___closed__8_value)}};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__9 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__9_value;
static const lean_string_object l_Std_Time_instReprWeekday_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Std.Time.Weekday.saturday"};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__10 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__10_value;
static const lean_ctor_object l_Std_Time_instReprWeekday_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWeekday_repr___closed__10_value)}};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__11 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__11_value;
static const lean_string_object l_Std_Time_instReprWeekday_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.Weekday.sunday"};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__12 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__12_value;
static const lean_ctor_object l_Std_Time_instReprWeekday_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWeekday_repr___closed__12_value)}};
static const lean_object* l_Std_Time_instReprWeekday_repr___closed__13 = (const lean_object*)&l_Std_Time_instReprWeekday_repr___closed__13_value;
static lean_once_cell_t l_Std_Time_instReprWeekday_repr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprWeekday_repr___closed__14;
static lean_once_cell_t l_Std_Time_instReprWeekday_repr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprWeekday_repr___closed__15;
LEAN_EXPORT lean_object* l_Std_Time_instReprWeekday_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprWeekday_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprWeekday___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprWeekday_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprWeekday___closed__0 = (const lean_object*)&l_Std_Time_instReprWeekday___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprWeekday = (const lean_object*)&l_Std_Time_instReprWeekday___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedWeekday_default;
LEAN_EXPORT uint8_t l_Std_Time_instInhabitedWeekday;
LEAN_EXPORT uint8_t l_Std_Time_Weekday_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqWeekday(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqWeekday___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Weekday_instReprOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Weekday_instReprOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Weekday_instReprOrdinal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Weekday_instReprOrdinal = (const lean_object*)&l_Std_Time_Weekday_instReprOrdinal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_Weekday_instDecidableEqOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instDecidableEqOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instLTOrdinal;
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instLEOrdinal;
LEAN_EXPORT uint8_t l_Std_Time_Weekday_instDecidableLeOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instDecidableLeOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Weekday_instDecidableLtOrdinal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instDecidableLtOrdinal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instOfNatOrdinal(lean_object*);
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__4;
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__5;
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__6;
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__7;
static lean_once_cell_t l_Std_Time_Weekday_instInhabitedOrdinal___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_instInhabitedOrdinal___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instInhabitedOrdinal;
static const lean_closure_object l_Std_Time_Weekday_instOrdOrdinal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Weekday_instOrdOrdinal___closed__0 = (const lean_object*)&l_Std_Time_Weekday_instOrdOrdinal___closed__0_value;
static const lean_closure_object l_Std_Time_Weekday_instOrdOrdinal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Weekday_instOrdOrdinal___closed__1 = (const lean_object*)&l_Std_Time_Weekday_instOrdOrdinal___closed__1_value;
static const lean_closure_object l_Std_Time_Weekday_instOrdOrdinal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Weekday_instOrdOrdinal___closed__1_value),((lean_object*)&l_Std_Time_Weekday_instOrdOrdinal___closed__0_value)} };
static const lean_object* l_Std_Time_Weekday_instOrdOrdinal___closed__2 = (const lean_object*)&l_Std_Time_Weekday_instOrdOrdinal___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_Weekday_instOrdOrdinal = (const lean_object*)&l_Std_Time_Weekday_instOrdOrdinal___closed__2_value;
static lean_once_cell_t l_Std_Time_Weekday_ofOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_ofOrdinal___closed__0;
LEAN_EXPORT uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofOrdinal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Weekday_toOrdinal_spec__0(lean_object*);
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__0;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__1;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__2;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__3;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__4;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__5;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__6;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__7;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__8;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__9;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__10;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__11;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__12;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__13;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__14;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__15;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__16;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__17;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__18;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__19;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__20;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__21;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__22;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__23;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__24;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__25;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__26;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__27;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__28;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__29;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__30;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__31;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__32;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__33;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__34;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__35;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__36;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__37;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__38;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__39;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__40;
static lean_once_cell_t l_Std_Time_Weekday_toOrdinal___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_toOrdinal___closed__41;
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toOrdinal___boxed(lean_object*);
static const lean_closure_object l_Std_Time_Weekday_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Weekday_toOrdinal___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Weekday_instOrd___closed__0 = (const lean_object*)&l_Std_Time_Weekday_instOrd___closed__0_value;
static const lean_closure_object l_Std_Time_Weekday_instOrd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_Weekday_instOrdOrdinal___closed__2_value),((lean_object*)&l_Std_Time_Weekday_instOrd___closed__0_value)} };
static const lean_object* l_Std_Time_Weekday_instOrd___closed__1 = (const lean_object*)&l_Std_Time_Weekday_instOrd___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Time_Weekday_instOrd = (const lean_object*)&l_Std_Time_Weekday_instOrd___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toNat(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toNat___boxed(lean_object*);
static const lean_ctor_object l_Std_Time_Weekday_ofNat_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Std_Time_Weekday_ofNat_x3f___closed__0 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x3f___closed__0_value;
static const lean_ctor_object l_Std_Time_Weekday_ofNat_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l_Std_Time_Weekday_ofNat_x3f___closed__1 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x3f___closed__1_value;
static const lean_ctor_object l_Std_Time_Weekday_ofNat_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Std_Time_Weekday_ofNat_x3f___closed__2 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x3f___closed__2_value;
static const lean_ctor_object l_Std_Time_Weekday_ofNat_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Std_Time_Weekday_ofNat_x3f___closed__3 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x3f___closed__3_value;
static const lean_ctor_object l_Std_Time_Weekday_ofNat_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Weekday_ofNat_x3f___closed__4 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x3f___closed__4_value;
static const lean_ctor_object l_Std_Time_Weekday_ofNat_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Weekday_ofNat_x3f___closed__5 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x3f___closed__5_value;
static const lean_ctor_object l_Std_Time_Weekday_ofNat_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Weekday_ofNat_x3f___closed__6 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x3f___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofNat_x3f___boxed(lean_object*);
static const lean_string_object l_Std_Time_Weekday_ofNat_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Time.Date.Unit.Weekday"};
static const lean_object* l_Std_Time_Weekday_ofNat_x21___closed__0 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x21___closed__0_value;
static const lean_string_object l_Std_Time_Weekday_ofNat_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.Time.Weekday.ofNat!"};
static const lean_object* l_Std_Time_Weekday_ofNat_x21___closed__1 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x21___closed__1_value;
static const lean_string_object l_Std_Time_Weekday_ofNat_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid weekday"};
static const lean_object* l_Std_Time_Weekday_ofNat_x21___closed__2 = (const lean_object*)&l_Std_Time_Weekday_ofNat_x21___closed__2_value;
static lean_once_cell_t l_Std_Time_Weekday_ofNat_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Weekday_ofNat_x21___closed__3;
LEAN_EXPORT uint8_t l_Std_Time_Weekday_ofNat_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofNat_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Weekday_next(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_next___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_Weekday_isWeekend(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_isWeekend___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
default: 
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_boxed_10_; lean_object* v_res_11_; 
v_x_boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Std_Time_Weekday_ctorIdx(v_x_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toCtorIdx(uint8_t v_x_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Std_Time_Weekday_ctorIdx(v_x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toCtorIdx___boxed(lean_object* v_x_14_){
_start:
{
uint8_t v_x_4__boxed_15_; lean_object* v_res_16_; 
v_x_4__boxed_15_ = lean_unbox(v_x_14_);
v_res_16_ = l_Std_Time_Weekday_toCtorIdx(v_x_4__boxed_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorElim___redArg(lean_object* v_k_17_){
_start:
{
lean_inc(v_k_17_);
return v_k_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorElim___redArg___boxed(lean_object* v_k_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Time_Weekday_ctorElim___redArg(v_k_18_);
lean_dec(v_k_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorElim(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, uint8_t v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_inc(v_k_24_);
return v_k_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ctorElim___boxed(lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
uint8_t v_t_boxed_30_; lean_object* v_res_31_; 
v_t_boxed_30_ = lean_unbox(v_t_27_);
v_res_31_ = l_Std_Time_Weekday_ctorElim(v_motive_25_, v_ctorIdx_26_, v_t_boxed_30_, v_h_28_, v_k_29_);
lean_dec(v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_monday_elim___redArg(lean_object* v_monday_32_){
_start:
{
lean_inc(v_monday_32_);
return v_monday_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_monday_elim___redArg___boxed(lean_object* v_monday_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_Time_Weekday_monday_elim___redArg(v_monday_33_);
lean_dec(v_monday_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_monday_elim(lean_object* v_motive_35_, uint8_t v_t_36_, lean_object* v_h_37_, lean_object* v_monday_38_){
_start:
{
lean_inc(v_monday_38_);
return v_monday_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_monday_elim___boxed(lean_object* v_motive_39_, lean_object* v_t_40_, lean_object* v_h_41_, lean_object* v_monday_42_){
_start:
{
uint8_t v_t_boxed_43_; lean_object* v_res_44_; 
v_t_boxed_43_ = lean_unbox(v_t_40_);
v_res_44_ = l_Std_Time_Weekday_monday_elim(v_motive_39_, v_t_boxed_43_, v_h_41_, v_monday_42_);
lean_dec(v_monday_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_tuesday_elim___redArg(lean_object* v_tuesday_45_){
_start:
{
lean_inc(v_tuesday_45_);
return v_tuesday_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_tuesday_elim___redArg___boxed(lean_object* v_tuesday_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Std_Time_Weekday_tuesday_elim___redArg(v_tuesday_46_);
lean_dec(v_tuesday_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_tuesday_elim(lean_object* v_motive_48_, uint8_t v_t_49_, lean_object* v_h_50_, lean_object* v_tuesday_51_){
_start:
{
lean_inc(v_tuesday_51_);
return v_tuesday_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_tuesday_elim___boxed(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_tuesday_55_){
_start:
{
uint8_t v_t_boxed_56_; lean_object* v_res_57_; 
v_t_boxed_56_ = lean_unbox(v_t_53_);
v_res_57_ = l_Std_Time_Weekday_tuesday_elim(v_motive_52_, v_t_boxed_56_, v_h_54_, v_tuesday_55_);
lean_dec(v_tuesday_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_wednesday_elim___redArg(lean_object* v_wednesday_58_){
_start:
{
lean_inc(v_wednesday_58_);
return v_wednesday_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_wednesday_elim___redArg___boxed(lean_object* v_wednesday_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Time_Weekday_wednesday_elim___redArg(v_wednesday_59_);
lean_dec(v_wednesday_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_wednesday_elim(lean_object* v_motive_61_, uint8_t v_t_62_, lean_object* v_h_63_, lean_object* v_wednesday_64_){
_start:
{
lean_inc(v_wednesday_64_);
return v_wednesday_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_wednesday_elim___boxed(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_wednesday_68_){
_start:
{
uint8_t v_t_boxed_69_; lean_object* v_res_70_; 
v_t_boxed_69_ = lean_unbox(v_t_66_);
v_res_70_ = l_Std_Time_Weekday_wednesday_elim(v_motive_65_, v_t_boxed_69_, v_h_67_, v_wednesday_68_);
lean_dec(v_wednesday_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_thursday_elim___redArg(lean_object* v_thursday_71_){
_start:
{
lean_inc(v_thursday_71_);
return v_thursday_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_thursday_elim___redArg___boxed(lean_object* v_thursday_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Time_Weekday_thursday_elim___redArg(v_thursday_72_);
lean_dec(v_thursday_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_thursday_elim(lean_object* v_motive_74_, uint8_t v_t_75_, lean_object* v_h_76_, lean_object* v_thursday_77_){
_start:
{
lean_inc(v_thursday_77_);
return v_thursday_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_thursday_elim___boxed(lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_thursday_81_){
_start:
{
uint8_t v_t_boxed_82_; lean_object* v_res_83_; 
v_t_boxed_82_ = lean_unbox(v_t_79_);
v_res_83_ = l_Std_Time_Weekday_thursday_elim(v_motive_78_, v_t_boxed_82_, v_h_80_, v_thursday_81_);
lean_dec(v_thursday_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_friday_elim___redArg(lean_object* v_friday_84_){
_start:
{
lean_inc(v_friday_84_);
return v_friday_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_friday_elim___redArg___boxed(lean_object* v_friday_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Time_Weekday_friday_elim___redArg(v_friday_85_);
lean_dec(v_friday_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_friday_elim(lean_object* v_motive_87_, uint8_t v_t_88_, lean_object* v_h_89_, lean_object* v_friday_90_){
_start:
{
lean_inc(v_friday_90_);
return v_friday_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_friday_elim___boxed(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_friday_94_){
_start:
{
uint8_t v_t_boxed_95_; lean_object* v_res_96_; 
v_t_boxed_95_ = lean_unbox(v_t_92_);
v_res_96_ = l_Std_Time_Weekday_friday_elim(v_motive_91_, v_t_boxed_95_, v_h_93_, v_friday_94_);
lean_dec(v_friday_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_saturday_elim___redArg(lean_object* v_saturday_97_){
_start:
{
lean_inc(v_saturday_97_);
return v_saturday_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_saturday_elim___redArg___boxed(lean_object* v_saturday_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_Time_Weekday_saturday_elim___redArg(v_saturday_98_);
lean_dec(v_saturday_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_saturday_elim(lean_object* v_motive_100_, uint8_t v_t_101_, lean_object* v_h_102_, lean_object* v_saturday_103_){
_start:
{
lean_inc(v_saturday_103_);
return v_saturday_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_saturday_elim___boxed(lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_saturday_107_){
_start:
{
uint8_t v_t_boxed_108_; lean_object* v_res_109_; 
v_t_boxed_108_ = lean_unbox(v_t_105_);
v_res_109_ = l_Std_Time_Weekday_saturday_elim(v_motive_104_, v_t_boxed_108_, v_h_106_, v_saturday_107_);
lean_dec(v_saturday_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_sunday_elim___redArg(lean_object* v_sunday_110_){
_start:
{
lean_inc(v_sunday_110_);
return v_sunday_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_sunday_elim___redArg___boxed(lean_object* v_sunday_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_Time_Weekday_sunday_elim___redArg(v_sunday_111_);
lean_dec(v_sunday_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_sunday_elim(lean_object* v_motive_113_, uint8_t v_t_114_, lean_object* v_h_115_, lean_object* v_sunday_116_){
_start:
{
lean_inc(v_sunday_116_);
return v_sunday_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_sunday_elim___boxed(lean_object* v_motive_117_, lean_object* v_t_118_, lean_object* v_h_119_, lean_object* v_sunday_120_){
_start:
{
uint8_t v_t_boxed_121_; lean_object* v_res_122_; 
v_t_boxed_121_ = lean_unbox(v_t_118_);
v_res_122_ = l_Std_Time_Weekday_sunday_elim(v_motive_117_, v_t_boxed_121_, v_h_119_, v_sunday_120_);
lean_dec(v_sunday_120_);
return v_res_122_;
}
}
static lean_object* _init_l_Std_Time_instReprWeekday_repr___closed__14(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(2u);
v___x_145_ = lean_nat_to_int(v___x_144_);
return v___x_145_;
}
}
static lean_object* _init_l_Std_Time_instReprWeekday_repr___closed__15(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_to_int(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWeekday_repr(uint8_t v_x_148_, lean_object* v_prec_149_){
_start:
{
lean_object* v___y_151_; lean_object* v___y_158_; lean_object* v___y_165_; lean_object* v___y_172_; lean_object* v___y_179_; lean_object* v___y_186_; lean_object* v___y_193_; 
switch(v_x_148_)
{
case 0:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(1024u);
v___x_200_ = lean_nat_dec_le(v___x_199_, v_prec_149_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__14, &l_Std_Time_instReprWeekday_repr___closed__14_once, _init_l_Std_Time_instReprWeekday_repr___closed__14);
v___y_151_ = v___x_201_;
goto v___jp_150_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___y_151_ = v___x_202_;
goto v___jp_150_;
}
}
case 1:
{
lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(1024u);
v___x_204_ = lean_nat_dec_le(v___x_203_, v_prec_149_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; 
v___x_205_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__14, &l_Std_Time_instReprWeekday_repr___closed__14_once, _init_l_Std_Time_instReprWeekday_repr___closed__14);
v___y_158_ = v___x_205_;
goto v___jp_157_;
}
else
{
lean_object* v___x_206_; 
v___x_206_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___y_158_ = v___x_206_;
goto v___jp_157_;
}
}
case 2:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1024u);
v___x_208_ = lean_nat_dec_le(v___x_207_, v_prec_149_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__14, &l_Std_Time_instReprWeekday_repr___closed__14_once, _init_l_Std_Time_instReprWeekday_repr___closed__14);
v___y_165_ = v___x_209_;
goto v___jp_164_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___y_165_ = v___x_210_;
goto v___jp_164_;
}
}
case 3:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1024u);
v___x_212_ = lean_nat_dec_le(v___x_211_, v_prec_149_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__14, &l_Std_Time_instReprWeekday_repr___closed__14_once, _init_l_Std_Time_instReprWeekday_repr___closed__14);
v___y_172_ = v___x_213_;
goto v___jp_171_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___y_172_ = v___x_214_;
goto v___jp_171_;
}
}
case 4:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(1024u);
v___x_216_ = lean_nat_dec_le(v___x_215_, v_prec_149_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__14, &l_Std_Time_instReprWeekday_repr___closed__14_once, _init_l_Std_Time_instReprWeekday_repr___closed__14);
v___y_179_ = v___x_217_;
goto v___jp_178_;
}
else
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___y_179_ = v___x_218_;
goto v___jp_178_;
}
}
case 5:
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(1024u);
v___x_220_ = lean_nat_dec_le(v___x_219_, v_prec_149_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__14, &l_Std_Time_instReprWeekday_repr___closed__14_once, _init_l_Std_Time_instReprWeekday_repr___closed__14);
v___y_186_ = v___x_221_;
goto v___jp_185_;
}
else
{
lean_object* v___x_222_; 
v___x_222_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___y_186_ = v___x_222_;
goto v___jp_185_;
}
}
default: 
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(1024u);
v___x_224_ = lean_nat_dec_le(v___x_223_, v_prec_149_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__14, &l_Std_Time_instReprWeekday_repr___closed__14_once, _init_l_Std_Time_instReprWeekday_repr___closed__14);
v___y_193_ = v___x_225_;
goto v___jp_192_;
}
else
{
lean_object* v___x_226_; 
v___x_226_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___y_193_ = v___x_226_;
goto v___jp_192_;
}
}
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_152_ = ((lean_object*)(l_Std_Time_instReprWeekday_repr___closed__1));
v___x_153_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_153_, 0, v___y_151_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = 0;
v___x_155_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set_uint8(v___x_155_, sizeof(void*)*1, v___x_154_);
v___x_156_ = l_Repr_addAppParen(v___x_155_, v_prec_149_);
return v___x_156_;
}
v___jp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_159_ = ((lean_object*)(l_Std_Time_instReprWeekday_repr___closed__3));
v___x_160_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_160_, 0, v___y_158_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = 0;
v___x_162_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_161_);
v___x_163_ = l_Repr_addAppParen(v___x_162_, v_prec_149_);
return v___x_163_;
}
v___jp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_166_ = ((lean_object*)(l_Std_Time_instReprWeekday_repr___closed__5));
v___x_167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_167_, 0, v___y_165_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = 0;
v___x_169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*1, v___x_168_);
v___x_170_ = l_Repr_addAppParen(v___x_169_, v_prec_149_);
return v___x_170_;
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_173_ = ((lean_object*)(l_Std_Time_instReprWeekday_repr___closed__7));
v___x_174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_174_, 0, v___y_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = 0;
v___x_176_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*1, v___x_175_);
v___x_177_ = l_Repr_addAppParen(v___x_176_, v_prec_149_);
return v___x_177_;
}
v___jp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_180_ = ((lean_object*)(l_Std_Time_instReprWeekday_repr___closed__9));
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___y_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = 0;
v___x_183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*1, v___x_182_);
v___x_184_ = l_Repr_addAppParen(v___x_183_, v_prec_149_);
return v___x_184_;
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = ((lean_object*)(l_Std_Time_instReprWeekday_repr___closed__11));
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = 0;
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = l_Repr_addAppParen(v___x_190_, v_prec_149_);
return v___x_191_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = ((lean_object*)(l_Std_Time_instReprWeekday_repr___closed__13));
v___x_195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_195_, 0, v___y_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = 0;
v___x_197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_196_);
v___x_198_ = l_Repr_addAppParen(v___x_197_, v_prec_149_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWeekday_repr___boxed(lean_object* v_x_227_, lean_object* v_prec_228_){
_start:
{
uint8_t v_x_401__boxed_229_; lean_object* v_res_230_; 
v_x_401__boxed_229_ = lean_unbox(v_x_227_);
v_res_230_ = l_Std_Time_instReprWeekday_repr(v_x_401__boxed_229_, v_prec_228_);
lean_dec(v_prec_228_);
return v_res_230_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedWeekday_default(void){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = 0;
return v___x_233_;
}
}
static uint8_t _init_l_Std_Time_instInhabitedWeekday(void){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = 0;
return v___x_234_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Weekday_ofNat(lean_object* v_n_235_){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(2u);
v___x_237_ = lean_nat_dec_le(v_n_235_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(4u);
v___x_239_ = lean_nat_dec_le(v_n_235_, v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(5u);
v___x_241_ = lean_nat_dec_le(v_n_235_, v___x_240_);
if (v___x_241_ == 0)
{
uint8_t v___x_242_; 
v___x_242_ = 6;
return v___x_242_;
}
else
{
uint8_t v___x_243_; 
v___x_243_ = 5;
return v___x_243_;
}
}
else
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(3u);
v___x_245_ = lean_nat_dec_le(v_n_235_, v___x_244_);
if (v___x_245_ == 0)
{
uint8_t v___x_246_; 
v___x_246_ = 4;
return v___x_246_;
}
else
{
uint8_t v___x_247_; 
v___x_247_ = 3;
return v___x_247_;
}
}
}
else
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_nat_dec_le(v_n_235_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_dec_le(v_n_235_, v___x_250_);
if (v___x_251_ == 0)
{
uint8_t v___x_252_; 
v___x_252_ = 2;
return v___x_252_;
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 1;
return v___x_253_;
}
}
else
{
uint8_t v___x_254_; 
v___x_254_ = 0;
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofNat___boxed(lean_object* v_n_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Std_Time_Weekday_ofNat(v_n_255_);
lean_dec(v_n_255_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqWeekday(uint8_t v_x_258_, uint8_t v_y_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_260_ = l_Std_Time_Weekday_ctorIdx(v_x_258_);
v___x_261_ = l_Std_Time_Weekday_ctorIdx(v_y_259_);
v___x_262_ = lean_nat_dec_eq(v___x_260_, v___x_261_);
lean_dec(v___x_261_);
lean_dec(v___x_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqWeekday___boxed(lean_object* v_x_263_, lean_object* v_y_264_){
_start:
{
uint8_t v_x_13__boxed_265_; uint8_t v_y_14__boxed_266_; uint8_t v_res_267_; lean_object* v_r_268_; 
v_x_13__boxed_265_ = lean_unbox(v_x_263_);
v_y_14__boxed_266_ = lean_unbox(v_y_264_);
v_res_267_ = l_Std_Time_instDecidableEqWeekday(v_x_13__boxed_265_, v_y_14__boxed_266_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Weekday_instDecidableEqOrdinal(lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lean_int_dec_eq(v_a_271_, v_b_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instDecidableEqOrdinal___boxed(lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Std_Time_Weekday_instDecidableEqOrdinal(v_a_274_, v_b_275_);
lean_dec(v_b_275_);
lean_dec(v_a_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instLTOrdinal(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instLEOrdinal(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_box(0);
return v___x_279_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Weekday_instDecidableLeOrdinal(lean_object* v_x_280_, lean_object* v_y_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = lean_int_dec_le(v_x_280_, v_y_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instDecidableLeOrdinal___boxed(lean_object* v_x_283_, lean_object* v_y_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_Time_Weekday_instDecidableLeOrdinal(v_x_283_, v_y_284_);
lean_dec(v_y_284_);
lean_dec(v_x_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Weekday_instDecidableLtOrdinal(lean_object* v_x_287_, lean_object* v_y_288_){
_start:
{
uint8_t v___x_289_; 
v___x_289_ = lean_int_dec_lt(v_x_287_, v_y_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instDecidableLtOrdinal___boxed(lean_object* v_x_290_, lean_object* v_y_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Std_Time_Weekday_instDecidableLtOrdinal(v_x_290_, v_y_291_);
lean_dec(v_y_291_);
lean_dec(v_x_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_instOfNatOrdinal(lean_object* v_n_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_296_ = lean_unsigned_to_nat(6u);
v___x_297_ = l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v___x_295_, v_n_294_, v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__0(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(6u);
v___x_299_ = lean_nat_to_int(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__0, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__0_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__0);
v___x_301_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_302_ = lean_int_add(v___x_301_, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__2(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_304_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__1, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__1_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__1);
v___x_305_ = lean_int_sub(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__3(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_range_308_; 
v___x_306_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_307_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__2, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__2_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__2);
v_range_308_ = lean_int_add(v___x_307_, v___x_306_);
return v_range_308_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__4(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_310_ = lean_int_sub(v___x_309_, v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__5(void){
_start:
{
lean_object* v_range_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_range_311_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__3, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__3);
v___x_312_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__4, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__4);
v___x_313_ = lean_int_emod(v___x_312_, v_range_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__6(void){
_start:
{
lean_object* v_range_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_range_314_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__3, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__3);
v___x_315_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__5, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__5_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__5);
v___x_316_ = lean_int_add(v___x_315_, v_range_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__7(void){
_start:
{
lean_object* v_range_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_range_317_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__3, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__3_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__3);
v___x_318_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__6, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__6_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__6);
v___x_319_ = lean_int_emod(v___x_318_, v_range_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__8(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_321_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__7, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__7_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__7);
v___x_322_ = lean_int_add(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Std_Time_Weekday_instInhabitedOrdinal(void){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__8, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__8_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__8);
return v___x_323_;
}
}
static lean_object* _init_l_Std_Time_Weekday_ofOrdinal___closed__0(void){
_start:
{
lean_object* v_natZero_330_; lean_object* v_intZero_331_; 
v_natZero_330_ = lean_unsigned_to_nat(0u);
v_intZero_331_ = lean_nat_to_int(v_natZero_330_);
return v_intZero_331_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Weekday_ofOrdinal(lean_object* v_x_332_){
_start:
{
lean_object* v_natZero_333_; lean_object* v_intZero_334_; uint8_t v_isNeg_335_; lean_object* v_a_336_; uint8_t v_isZero_337_; lean_object* v_one_338_; lean_object* v_n_339_; uint8_t v_isZero_340_; 
v_natZero_333_ = lean_unsigned_to_nat(0u);
v_intZero_334_ = lean_obj_once(&l_Std_Time_Weekday_ofOrdinal___closed__0, &l_Std_Time_Weekday_ofOrdinal___closed__0_once, _init_l_Std_Time_Weekday_ofOrdinal___closed__0);
v_isNeg_335_ = lean_int_dec_lt(v_x_332_, v_intZero_334_);
v_a_336_ = lean_nat_abs(v_x_332_);
v_isZero_337_ = lean_nat_dec_eq(v_a_336_, v_natZero_333_);
v_one_338_ = lean_unsigned_to_nat(1u);
v_n_339_ = lean_nat_sub(v_a_336_, v_one_338_);
lean_dec(v_a_336_);
v_isZero_340_ = lean_nat_dec_eq(v_n_339_, v_natZero_333_);
if (v_isZero_340_ == 1)
{
uint8_t v___x_341_; 
lean_dec(v_n_339_);
v___x_341_ = 0;
return v___x_341_;
}
else
{
lean_object* v_n_342_; uint8_t v_isZero_343_; 
v_n_342_ = lean_nat_sub(v_n_339_, v_one_338_);
lean_dec(v_n_339_);
v_isZero_343_ = lean_nat_dec_eq(v_n_342_, v_natZero_333_);
if (v_isZero_343_ == 1)
{
uint8_t v___x_344_; 
lean_dec(v_n_342_);
v___x_344_ = 1;
return v___x_344_;
}
else
{
lean_object* v_n_345_; uint8_t v_isZero_346_; 
v_n_345_ = lean_nat_sub(v_n_342_, v_one_338_);
lean_dec(v_n_342_);
v_isZero_346_ = lean_nat_dec_eq(v_n_345_, v_natZero_333_);
if (v_isZero_346_ == 1)
{
uint8_t v___x_347_; 
lean_dec(v_n_345_);
v___x_347_ = 2;
return v___x_347_;
}
else
{
lean_object* v_n_348_; uint8_t v_isZero_349_; 
v_n_348_ = lean_nat_sub(v_n_345_, v_one_338_);
lean_dec(v_n_345_);
v_isZero_349_ = lean_nat_dec_eq(v_n_348_, v_natZero_333_);
if (v_isZero_349_ == 1)
{
uint8_t v___x_350_; 
lean_dec(v_n_348_);
v___x_350_ = 3;
return v___x_350_;
}
else
{
lean_object* v_n_351_; uint8_t v_isZero_352_; 
v_n_351_ = lean_nat_sub(v_n_348_, v_one_338_);
lean_dec(v_n_348_);
v_isZero_352_ = lean_nat_dec_eq(v_n_351_, v_natZero_333_);
if (v_isZero_352_ == 1)
{
uint8_t v___x_353_; 
lean_dec(v_n_351_);
v___x_353_ = 4;
return v___x_353_;
}
else
{
lean_object* v_n_354_; uint8_t v_isZero_355_; 
v_n_354_ = lean_nat_sub(v_n_351_, v_one_338_);
lean_dec(v_n_351_);
v_isZero_355_ = lean_nat_dec_eq(v_n_354_, v_natZero_333_);
if (v_isZero_355_ == 1)
{
uint8_t v___x_356_; 
lean_dec(v_n_354_);
v___x_356_ = 5;
return v___x_356_;
}
else
{
lean_object* v_n_357_; uint8_t v_isZero_358_; uint8_t v___x_359_; 
v_n_357_ = lean_nat_sub(v_n_354_, v_one_338_);
lean_dec(v_n_354_);
v_isZero_358_ = lean_nat_dec_eq(v_n_357_, v_natZero_333_);
lean_dec(v_n_357_);
v___x_359_ = 6;
return v___x_359_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofOrdinal___boxed(lean_object* v_x_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_Time_Weekday_ofOrdinal(v_x_360_);
lean_dec(v_x_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_Weekday_toOrdinal_spec__0(lean_object* v_a_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_nat_to_int(v_a_363_);
return v___x_364_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__0(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_unsigned_to_nat(6u);
v___x_366_ = lean_nat_to_int(v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__1(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__0, &l_Std_Time_Weekday_toOrdinal___closed__0_once, _init_l_Std_Time_Weekday_toOrdinal___closed__0);
v___x_368_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_369_ = lean_int_add(v___x_368_, v___x_367_);
return v___x_369_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__2(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_370_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_371_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__1, &l_Std_Time_Weekday_toOrdinal___closed__1_once, _init_l_Std_Time_Weekday_toOrdinal___closed__1);
v___x_372_ = lean_int_sub(v___x_371_, v___x_370_);
return v___x_372_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__3(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_range_375_; 
v___x_373_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_374_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__2, &l_Std_Time_Weekday_toOrdinal___closed__2_once, _init_l_Std_Time_Weekday_toOrdinal___closed__2);
v_range_375_ = lean_int_add(v___x_374_, v___x_373_);
return v_range_375_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__4(void){
_start:
{
lean_object* v_range_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_range_376_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_377_ = lean_obj_once(&l_Std_Time_Weekday_instInhabitedOrdinal___closed__4, &l_Std_Time_Weekday_instInhabitedOrdinal___closed__4_once, _init_l_Std_Time_Weekday_instInhabitedOrdinal___closed__4);
v___x_378_ = lean_int_emod(v___x_377_, v_range_376_);
return v___x_378_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__5(void){
_start:
{
lean_object* v_range_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_range_379_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_380_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__4, &l_Std_Time_Weekday_toOrdinal___closed__4_once, _init_l_Std_Time_Weekday_toOrdinal___closed__4);
v___x_381_ = lean_int_add(v___x_380_, v_range_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__6(void){
_start:
{
lean_object* v_range_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_range_382_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_383_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__5, &l_Std_Time_Weekday_toOrdinal___closed__5_once, _init_l_Std_Time_Weekday_toOrdinal___closed__5);
v___x_384_ = lean_int_emod(v___x_383_, v_range_382_);
return v___x_384_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__7(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_386_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__6, &l_Std_Time_Weekday_toOrdinal___closed__6_once, _init_l_Std_Time_Weekday_toOrdinal___closed__6);
v___x_387_ = lean_int_add(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__8(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_389_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__14, &l_Std_Time_instReprWeekday_repr___closed__14_once, _init_l_Std_Time_instReprWeekday_repr___closed__14);
v___x_390_ = lean_int_sub(v___x_389_, v___x_388_);
return v___x_390_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__9(void){
_start:
{
lean_object* v_range_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_range_391_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_392_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__8, &l_Std_Time_Weekday_toOrdinal___closed__8_once, _init_l_Std_Time_Weekday_toOrdinal___closed__8);
v___x_393_ = lean_int_emod(v___x_392_, v_range_391_);
return v___x_393_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__10(void){
_start:
{
lean_object* v_range_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_range_394_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_395_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__9, &l_Std_Time_Weekday_toOrdinal___closed__9_once, _init_l_Std_Time_Weekday_toOrdinal___closed__9);
v___x_396_ = lean_int_add(v___x_395_, v_range_394_);
return v___x_396_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__11(void){
_start:
{
lean_object* v_range_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_range_397_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_398_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__10, &l_Std_Time_Weekday_toOrdinal___closed__10_once, _init_l_Std_Time_Weekday_toOrdinal___closed__10);
v___x_399_ = lean_int_emod(v___x_398_, v_range_397_);
return v___x_399_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__12(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_401_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__11, &l_Std_Time_Weekday_toOrdinal___closed__11_once, _init_l_Std_Time_Weekday_toOrdinal___closed__11);
v___x_402_ = lean_int_add(v___x_401_, v___x_400_);
return v___x_402_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__13(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(3u);
v___x_404_ = lean_nat_to_int(v___x_403_);
return v___x_404_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__14(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_406_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__13, &l_Std_Time_Weekday_toOrdinal___closed__13_once, _init_l_Std_Time_Weekday_toOrdinal___closed__13);
v___x_407_ = lean_int_sub(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__15(void){
_start:
{
lean_object* v_range_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_range_408_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_409_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__14, &l_Std_Time_Weekday_toOrdinal___closed__14_once, _init_l_Std_Time_Weekday_toOrdinal___closed__14);
v___x_410_ = lean_int_emod(v___x_409_, v_range_408_);
return v___x_410_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__16(void){
_start:
{
lean_object* v_range_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_range_411_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_412_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__15, &l_Std_Time_Weekday_toOrdinal___closed__15_once, _init_l_Std_Time_Weekday_toOrdinal___closed__15);
v___x_413_ = lean_int_add(v___x_412_, v_range_411_);
return v___x_413_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__17(void){
_start:
{
lean_object* v_range_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_range_414_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_415_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__16, &l_Std_Time_Weekday_toOrdinal___closed__16_once, _init_l_Std_Time_Weekday_toOrdinal___closed__16);
v___x_416_ = lean_int_emod(v___x_415_, v_range_414_);
return v___x_416_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__18(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_418_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__17, &l_Std_Time_Weekday_toOrdinal___closed__17_once, _init_l_Std_Time_Weekday_toOrdinal___closed__17);
v___x_419_ = lean_int_add(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__19(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(4u);
v___x_421_ = lean_nat_to_int(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__20(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_423_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__19, &l_Std_Time_Weekday_toOrdinal___closed__19_once, _init_l_Std_Time_Weekday_toOrdinal___closed__19);
v___x_424_ = lean_int_sub(v___x_423_, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__21(void){
_start:
{
lean_object* v_range_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_range_425_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_426_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__20, &l_Std_Time_Weekday_toOrdinal___closed__20_once, _init_l_Std_Time_Weekday_toOrdinal___closed__20);
v___x_427_ = lean_int_emod(v___x_426_, v_range_425_);
return v___x_427_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__22(void){
_start:
{
lean_object* v_range_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_range_428_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_429_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__21, &l_Std_Time_Weekday_toOrdinal___closed__21_once, _init_l_Std_Time_Weekday_toOrdinal___closed__21);
v___x_430_ = lean_int_add(v___x_429_, v_range_428_);
return v___x_430_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__23(void){
_start:
{
lean_object* v_range_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_range_431_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_432_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__22, &l_Std_Time_Weekday_toOrdinal___closed__22_once, _init_l_Std_Time_Weekday_toOrdinal___closed__22);
v___x_433_ = lean_int_emod(v___x_432_, v_range_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__24(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_435_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__23, &l_Std_Time_Weekday_toOrdinal___closed__23_once, _init_l_Std_Time_Weekday_toOrdinal___closed__23);
v___x_436_ = lean_int_add(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__25(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(5u);
v___x_438_ = lean_nat_to_int(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__26(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_440_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__25, &l_Std_Time_Weekday_toOrdinal___closed__25_once, _init_l_Std_Time_Weekday_toOrdinal___closed__25);
v___x_441_ = lean_int_sub(v___x_440_, v___x_439_);
return v___x_441_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__27(void){
_start:
{
lean_object* v_range_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_range_442_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_443_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__26, &l_Std_Time_Weekday_toOrdinal___closed__26_once, _init_l_Std_Time_Weekday_toOrdinal___closed__26);
v___x_444_ = lean_int_emod(v___x_443_, v_range_442_);
return v___x_444_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__28(void){
_start:
{
lean_object* v_range_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_range_445_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_446_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__27, &l_Std_Time_Weekday_toOrdinal___closed__27_once, _init_l_Std_Time_Weekday_toOrdinal___closed__27);
v___x_447_ = lean_int_add(v___x_446_, v_range_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__29(void){
_start:
{
lean_object* v_range_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_range_448_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_449_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__28, &l_Std_Time_Weekday_toOrdinal___closed__28_once, _init_l_Std_Time_Weekday_toOrdinal___closed__28);
v___x_450_ = lean_int_emod(v___x_449_, v_range_448_);
return v___x_450_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__30(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_452_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__29, &l_Std_Time_Weekday_toOrdinal___closed__29_once, _init_l_Std_Time_Weekday_toOrdinal___closed__29);
v___x_453_ = lean_int_add(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__31(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_455_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__0, &l_Std_Time_Weekday_toOrdinal___closed__0_once, _init_l_Std_Time_Weekday_toOrdinal___closed__0);
v___x_456_ = lean_int_sub(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__32(void){
_start:
{
lean_object* v_range_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v_range_457_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_458_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__31, &l_Std_Time_Weekday_toOrdinal___closed__31_once, _init_l_Std_Time_Weekday_toOrdinal___closed__31);
v___x_459_ = lean_int_emod(v___x_458_, v_range_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__33(void){
_start:
{
lean_object* v_range_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_range_460_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_461_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__32, &l_Std_Time_Weekday_toOrdinal___closed__32_once, _init_l_Std_Time_Weekday_toOrdinal___closed__32);
v___x_462_ = lean_int_add(v___x_461_, v_range_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__34(void){
_start:
{
lean_object* v_range_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_range_463_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_464_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__33, &l_Std_Time_Weekday_toOrdinal___closed__33_once, _init_l_Std_Time_Weekday_toOrdinal___closed__33);
v___x_465_ = lean_int_emod(v___x_464_, v_range_463_);
return v___x_465_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__35(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_467_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__34, &l_Std_Time_Weekday_toOrdinal___closed__34_once, _init_l_Std_Time_Weekday_toOrdinal___closed__34);
v___x_468_ = lean_int_add(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__36(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(7u);
v___x_470_ = lean_nat_to_int(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__37(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_472_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__36, &l_Std_Time_Weekday_toOrdinal___closed__36_once, _init_l_Std_Time_Weekday_toOrdinal___closed__36);
v___x_473_ = lean_int_sub(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__38(void){
_start:
{
lean_object* v_range_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_range_474_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_475_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__37, &l_Std_Time_Weekday_toOrdinal___closed__37_once, _init_l_Std_Time_Weekday_toOrdinal___closed__37);
v___x_476_ = lean_int_emod(v___x_475_, v_range_474_);
return v___x_476_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__39(void){
_start:
{
lean_object* v_range_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_range_477_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_478_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__38, &l_Std_Time_Weekday_toOrdinal___closed__38_once, _init_l_Std_Time_Weekday_toOrdinal___closed__38);
v___x_479_ = lean_int_add(v___x_478_, v_range_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__40(void){
_start:
{
lean_object* v_range_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_range_480_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__3, &l_Std_Time_Weekday_toOrdinal___closed__3_once, _init_l_Std_Time_Weekday_toOrdinal___closed__3);
v___x_481_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__39, &l_Std_Time_Weekday_toOrdinal___closed__39_once, _init_l_Std_Time_Weekday_toOrdinal___closed__39);
v___x_482_ = lean_int_emod(v___x_481_, v_range_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Std_Time_Weekday_toOrdinal___closed__41(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_obj_once(&l_Std_Time_instReprWeekday_repr___closed__15, &l_Std_Time_instReprWeekday_repr___closed__15_once, _init_l_Std_Time_instReprWeekday_repr___closed__15);
v___x_484_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__40, &l_Std_Time_Weekday_toOrdinal___closed__40_once, _init_l_Std_Time_Weekday_toOrdinal___closed__40);
v___x_485_ = lean_int_add(v___x_484_, v___x_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toOrdinal(uint8_t v_x_486_){
_start:
{
switch(v_x_486_)
{
case 0:
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__7, &l_Std_Time_Weekday_toOrdinal___closed__7_once, _init_l_Std_Time_Weekday_toOrdinal___closed__7);
return v___x_487_;
}
case 1:
{
lean_object* v___x_488_; 
v___x_488_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__12, &l_Std_Time_Weekday_toOrdinal___closed__12_once, _init_l_Std_Time_Weekday_toOrdinal___closed__12);
return v___x_488_;
}
case 2:
{
lean_object* v___x_489_; 
v___x_489_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__18, &l_Std_Time_Weekday_toOrdinal___closed__18_once, _init_l_Std_Time_Weekday_toOrdinal___closed__18);
return v___x_489_;
}
case 3:
{
lean_object* v___x_490_; 
v___x_490_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__24, &l_Std_Time_Weekday_toOrdinal___closed__24_once, _init_l_Std_Time_Weekday_toOrdinal___closed__24);
return v___x_490_;
}
case 4:
{
lean_object* v___x_491_; 
v___x_491_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__30, &l_Std_Time_Weekday_toOrdinal___closed__30_once, _init_l_Std_Time_Weekday_toOrdinal___closed__30);
return v___x_491_;
}
case 5:
{
lean_object* v___x_492_; 
v___x_492_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__35, &l_Std_Time_Weekday_toOrdinal___closed__35_once, _init_l_Std_Time_Weekday_toOrdinal___closed__35);
return v___x_492_;
}
default: 
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l_Std_Time_Weekday_toOrdinal___closed__41, &l_Std_Time_Weekday_toOrdinal___closed__41_once, _init_l_Std_Time_Weekday_toOrdinal___closed__41);
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toOrdinal___boxed(lean_object* v_x_494_){
_start:
{
uint8_t v_x_611__boxed_495_; lean_object* v_res_496_; 
v_x_611__boxed_495_ = lean_unbox(v_x_494_);
v_res_496_ = l_Std_Time_Weekday_toOrdinal(v_x_611__boxed_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg(uint8_t v_x_502_, lean_object* v_h__1_503_, lean_object* v_h__2_504_, lean_object* v_h__3_505_, lean_object* v_h__4_506_, lean_object* v_h__5_507_, lean_object* v_h__6_508_, lean_object* v_h__7_509_){
_start:
{
switch(v_x_502_)
{
case 0:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_h__7_509_);
lean_dec(v_h__6_508_);
lean_dec(v_h__5_507_);
lean_dec(v_h__4_506_);
lean_dec(v_h__3_505_);
lean_dec(v_h__2_504_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_apply_1(v_h__1_503_, v___x_510_);
return v___x_511_;
}
case 1:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_h__7_509_);
lean_dec(v_h__6_508_);
lean_dec(v_h__5_507_);
lean_dec(v_h__4_506_);
lean_dec(v_h__3_505_);
lean_dec(v_h__1_503_);
v___x_512_ = lean_box(0);
v___x_513_ = lean_apply_1(v_h__2_504_, v___x_512_);
return v___x_513_;
}
case 2:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v_h__7_509_);
lean_dec(v_h__6_508_);
lean_dec(v_h__5_507_);
lean_dec(v_h__4_506_);
lean_dec(v_h__2_504_);
lean_dec(v_h__1_503_);
v___x_514_ = lean_box(0);
v___x_515_ = lean_apply_1(v_h__3_505_, v___x_514_);
return v___x_515_;
}
case 3:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v_h__7_509_);
lean_dec(v_h__6_508_);
lean_dec(v_h__5_507_);
lean_dec(v_h__3_505_);
lean_dec(v_h__2_504_);
lean_dec(v_h__1_503_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_apply_1(v_h__4_506_, v___x_516_);
return v___x_517_;
}
case 4:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_h__7_509_);
lean_dec(v_h__6_508_);
lean_dec(v_h__4_506_);
lean_dec(v_h__3_505_);
lean_dec(v_h__2_504_);
lean_dec(v_h__1_503_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_apply_1(v_h__5_507_, v___x_518_);
return v___x_519_;
}
case 5:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_h__7_509_);
lean_dec(v_h__5_507_);
lean_dec(v_h__4_506_);
lean_dec(v_h__3_505_);
lean_dec(v_h__2_504_);
lean_dec(v_h__1_503_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_apply_1(v_h__6_508_, v___x_520_);
return v___x_521_;
}
default: 
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_h__6_508_);
lean_dec(v_h__5_507_);
lean_dec(v_h__4_506_);
lean_dec(v_h__3_505_);
lean_dec(v_h__2_504_);
lean_dec(v_h__1_503_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_1(v_h__7_509_, v___x_522_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg___boxed(lean_object* v_x_524_, lean_object* v_h__1_525_, lean_object* v_h__2_526_, lean_object* v_h__3_527_, lean_object* v_h__4_528_, lean_object* v_h__5_529_, lean_object* v_h__6_530_, lean_object* v_h__7_531_){
_start:
{
uint8_t v_x_62__boxed_532_; lean_object* v_res_533_; 
v_x_62__boxed_532_ = lean_unbox(v_x_524_);
v_res_533_ = l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg(v_x_62__boxed_532_, v_h__1_525_, v_h__2_526_, v_h__3_527_, v_h__4_528_, v_h__5_529_, v_h__6_530_, v_h__7_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter(lean_object* v_motive_534_, uint8_t v_x_535_, lean_object* v_h__1_536_, lean_object* v_h__2_537_, lean_object* v_h__3_538_, lean_object* v_h__4_539_, lean_object* v_h__5_540_, lean_object* v_h__6_541_, lean_object* v_h__7_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___redArg(v_x_535_, v_h__1_536_, v_h__2_537_, v_h__3_538_, v_h__4_539_, v_h__5_540_, v_h__6_541_, v_h__7_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter___boxed(lean_object* v_motive_544_, lean_object* v_x_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_, lean_object* v_h__3_548_, lean_object* v_h__4_549_, lean_object* v_h__5_550_, lean_object* v_h__6_551_, lean_object* v_h__7_552_){
_start:
{
uint8_t v_x_93__boxed_553_; lean_object* v_res_554_; 
v_x_93__boxed_553_ = lean_unbox(v_x_545_);
v_res_554_ = l___private_Std_Time_Date_Unit_Weekday_0__Std_Time_instReprWeekday_repr_match__1_splitter(v_motive_544_, v_x_93__boxed_553_, v_h__1_546_, v_h__2_547_, v_h__3_548_, v_h__4_549_, v_h__5_550_, v_h__6_551_, v_h__7_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toNat(uint8_t v_x_555_){
_start:
{
switch(v_x_555_)
{
case 0:
{
lean_object* v___x_556_; 
v___x_556_ = lean_unsigned_to_nat(1u);
return v___x_556_;
}
case 1:
{
lean_object* v___x_557_; 
v___x_557_ = lean_unsigned_to_nat(2u);
return v___x_557_;
}
case 2:
{
lean_object* v___x_558_; 
v___x_558_ = lean_unsigned_to_nat(3u);
return v___x_558_;
}
case 3:
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(4u);
return v___x_559_;
}
case 4:
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(5u);
return v___x_560_;
}
case 5:
{
lean_object* v___x_561_; 
v___x_561_ = lean_unsigned_to_nat(6u);
return v___x_561_;
}
default: 
{
lean_object* v___x_562_; 
v___x_562_ = lean_unsigned_to_nat(7u);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_toNat___boxed(lean_object* v_x_563_){
_start:
{
uint8_t v_x_74__boxed_564_; lean_object* v_res_565_; 
v_x_74__boxed_564_ = lean_unbox(v_x_563_);
v_res_565_ = l_Std_Time_Weekday_toNat(v_x_74__boxed_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofNat_x3f(lean_object* v_x_587_){
_start:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_dec_eq(v_x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(2u);
v___x_591_ = lean_nat_dec_eq(v_x_587_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_unsigned_to_nat(3u);
v___x_593_ = lean_nat_dec_eq(v_x_587_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(4u);
v___x_595_ = lean_nat_dec_eq(v_x_587_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(5u);
v___x_597_ = lean_nat_dec_eq(v_x_587_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_unsigned_to_nat(6u);
v___x_599_ = lean_nat_dec_eq(v_x_587_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(7u);
v___x_601_ = lean_nat_dec_eq(v_x_587_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_box(0);
return v___x_602_;
}
else
{
lean_object* v___x_603_; 
v___x_603_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x3f___closed__0));
return v___x_603_;
}
}
else
{
lean_object* v___x_604_; 
v___x_604_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x3f___closed__1));
return v___x_604_;
}
}
else
{
lean_object* v___x_605_; 
v___x_605_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x3f___closed__2));
return v___x_605_;
}
}
else
{
lean_object* v___x_606_; 
v___x_606_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x3f___closed__3));
return v___x_606_;
}
}
else
{
lean_object* v___x_607_; 
v___x_607_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x3f___closed__4));
return v___x_607_;
}
}
else
{
lean_object* v___x_608_; 
v___x_608_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x3f___closed__5));
return v___x_608_;
}
}
else
{
lean_object* v___x_609_; 
v___x_609_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x3f___closed__6));
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofNat_x3f___boxed(lean_object* v_x_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Time_Weekday_ofNat_x3f(v_x_610_);
lean_dec(v_x_610_);
return v_res_611_;
}
}
static lean_object* _init_l_Std_Time_Weekday_ofNat_x21___closed__3(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_615_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x21___closed__2));
v___x_616_ = lean_unsigned_to_nat(12u);
v___x_617_ = lean_unsigned_to_nat(139u);
v___x_618_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x21___closed__1));
v___x_619_ = ((lean_object*)(l_Std_Time_Weekday_ofNat_x21___closed__0));
v___x_620_ = l_mkPanicMessageWithDecl(v___x_619_, v___x_618_, v___x_617_, v___x_616_, v___x_615_);
return v___x_620_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Weekday_ofNat_x21(lean_object* v_n_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_Time_Weekday_ofNat_x3f(v_n_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_623_ = 0;
v___x_624_ = lean_obj_once(&l_Std_Time_Weekday_ofNat_x21___closed__3, &l_Std_Time_Weekday_ofNat_x21___closed__3_once, _init_l_Std_Time_Weekday_ofNat_x21___closed__3);
v___x_625_ = lean_box(v___x_623_);
v___x_626_ = l_panic___redArg(v___x_625_, v___x_624_);
v___x_627_ = lean_unbox(v___x_626_);
lean_dec(v___x_626_);
return v___x_627_;
}
else
{
lean_object* v_val_628_; uint8_t v___x_629_; 
v_val_628_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_val_628_);
lean_dec_ref(v___x_622_);
v___x_629_ = lean_unbox(v_val_628_);
lean_dec(v_val_628_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_ofNat_x21___boxed(lean_object* v_n_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l_Std_Time_Weekday_ofNat_x21(v_n_630_);
lean_dec(v_n_630_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Weekday_next(uint8_t v_x_633_){
_start:
{
switch(v_x_633_)
{
case 0:
{
uint8_t v___x_634_; 
v___x_634_ = 1;
return v___x_634_;
}
case 1:
{
uint8_t v___x_635_; 
v___x_635_ = 2;
return v___x_635_;
}
case 2:
{
uint8_t v___x_636_; 
v___x_636_ = 3;
return v___x_636_;
}
case 3:
{
uint8_t v___x_637_; 
v___x_637_ = 4;
return v___x_637_;
}
case 4:
{
uint8_t v___x_638_; 
v___x_638_ = 5;
return v___x_638_;
}
case 5:
{
uint8_t v___x_639_; 
v___x_639_ = 6;
return v___x_639_;
}
default: 
{
uint8_t v___x_640_; 
v___x_640_ = 0;
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_next___boxed(lean_object* v_x_641_){
_start:
{
uint8_t v_x_53__boxed_642_; uint8_t v_res_643_; lean_object* v_r_644_; 
v_x_53__boxed_642_ = lean_unbox(v_x_641_);
v_res_643_ = l_Std_Time_Weekday_next(v_x_53__boxed_642_);
v_r_644_ = lean_box(v_res_643_);
return v_r_644_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_Weekday_isWeekend(uint8_t v_x_645_){
_start:
{
switch(v_x_645_)
{
case 5:
{
uint8_t v___x_646_; 
v___x_646_ = 1;
return v___x_646_;
}
case 6:
{
uint8_t v___x_647_; 
v___x_647_ = 1;
return v___x_647_;
}
default: 
{
uint8_t v___x_648_; 
v___x_648_ = 0;
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Weekday_isWeekend___boxed(lean_object* v_x_649_){
_start:
{
uint8_t v_x_26__boxed_650_; uint8_t v_res_651_; lean_object* v_r_652_; 
v_x_26__boxed_650_ = lean_unbox(v_x_649_);
v_res_651_ = l_Std_Time_Weekday_isWeekend(v_x_26__boxed_650_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Day(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedWeekday_default = _init_l_Std_Time_instInhabitedWeekday_default();
l_Std_Time_instInhabitedWeekday = _init_l_Std_Time_instInhabitedWeekday();
l_Std_Time_Weekday_instLTOrdinal = _init_l_Std_Time_Weekday_instLTOrdinal();
lean_mark_persistent(l_Std_Time_Weekday_instLTOrdinal);
l_Std_Time_Weekday_instLEOrdinal = _init_l_Std_Time_Weekday_instLEOrdinal();
lean_mark_persistent(l_Std_Time_Weekday_instLEOrdinal);
l_Std_Time_Weekday_instInhabitedOrdinal = _init_l_Std_Time_Weekday_instInhabitedOrdinal();
lean_mark_persistent(l_Std_Time_Weekday_instInhabitedOrdinal);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Date_Unit_Day(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Unit_Day(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Weekday(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Date_Unit_Weekday(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Date_Unit_Weekday(builtin);
}
#ifdef __cplusplus
}
#endif
