// Lean compiler output
// Module: Std.Time.Zoned.ZoneRules
// Imports: public import Std.Time.Zoned.TimeZone public import Std.Time.DateTime.Timestamp public import Std.Time.DateTime.WallTime public import Std.Time.Zoned.RecurringRule
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
lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
uint8_t l_Std_Time_Duration_instDecidableLt(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
lean_object* l_Std_Time_TimeZone_TransitionSpec_toEpochDay(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_Second_instReprOffset___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprUTLocal_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Time.TimeZone.UTLocal.ut"};
static const lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1_value;
static const lean_string_object l_Std_Time_TimeZone_instReprUTLocal_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Time.TimeZone.UTLocal.local"};
static const lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4;
static lean_once_cell_t l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprUTLocal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprUTLocal_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprUTLocal___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprUTLocal___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprUTLocal = (const lean_object*)&l_Std_Time_TimeZone_instReprUTLocal___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instInhabitedUTLocal_default;
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instInhabitedUTLocal;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprStdWall_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Std.Time.TimeZone.StdWall.wall"};
static const lean_object* l_Std_Time_TimeZone_instReprStdWall_repr___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprStdWall_repr___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprStdWall_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprStdWall_repr___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprStdWall_repr___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprStdWall_repr___closed__1_value;
static const lean_string_object l_Std_Time_TimeZone_instReprStdWall_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Time.TimeZone.StdWall.standard"};
static const lean_object* l_Std_Time_TimeZone_instReprStdWall_repr___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprStdWall_repr___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprStdWall_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprStdWall_repr___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprStdWall_repr___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprStdWall_repr___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprStdWall_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprStdWall_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprStdWall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprStdWall_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprStdWall___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprStdWall___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprStdWall = (const lean_object*)&l_Std_Time_TimeZone_instReprStdWall___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instInhabitedStdWall_default;
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instInhabitedStdWall;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instReprLocalTimeType_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "gmtOffset"};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isDst"};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "abbreviation"};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "wall"};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__16_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__16_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "utLocal"};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__19 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__19_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__19_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "identifier"};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__22 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__22_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__22_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24;
static const lean_string_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__25 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__25_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26;
static lean_once_cell_t l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__25_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprLocalTimeType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprLocalTimeType_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprLocalTimeType = (const lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType___closed__0_value;
static lean_once_cell_t l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0;
static const lean_string_object l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1_value;
static lean_once_cell_t l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instInhabitedLocalTimeType_default_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedLocalTimeType;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone___boxed(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "time"};
static const lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "localTimeType"};
static const lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprTransition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprTransition_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprTransition___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprTransition___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprTransition = (const lean_object*)&l_Std_Time_TimeZone_instReprTransition___closed__0_value;
static lean_once_cell_t l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0;
static lean_once_cell_t l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedTransition_default;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedTransition;
static const lean_string_object l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__0 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__1 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__1_value;
static const lean_string_object l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__2 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__3 = (const lean_object*)&l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1_value;
static const lean_string_object l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__2_value;
static lean_once_cell_t l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3;
static lean_once_cell_t l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4;
static const lean_ctor_object l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5_value;
static const lean_ctor_object l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__2_value)}};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6_value;
static const lean_string_object l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__7_value)}};
static const lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "initialLocalTimeType"};
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4;
static const lean_string_object l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "transitions"};
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "transitionRule"};
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__9_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprZoneRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprZoneRules_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprZoneRules___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprZoneRules = (const lean_object*)&l_Std_Time_TimeZone_instReprZoneRules___closed__0_value;
static const lean_array_object l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0_value;
static lean_once_cell_t l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedZoneRules_default;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedZoneRules;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timestamp(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_Transition_timezoneAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "cannot find local timezone."};
static const lean_object* l_Std_Time_TimeZone_Transition_timezoneAt___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_Transition_timezoneAt___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_Transition_timezoneAt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_Transition_timezoneAt___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_Transition_timezoneAt___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_Transition_timezoneAt___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds_spec__0(lean_object*);
static lean_once_cell_t l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(lean_object*, lean_object*);
static const lean_array_object l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_TimeZone_ZoneRules_UTC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_ZoneRules_UTC___closed__0;
static const lean_string_object l_Std_Time_TimeZone_ZoneRules_UTC___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l_Std_Time_TimeZone_ZoneRules_UTC___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_ZoneRules_UTC___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_ZoneRules_UTC___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_ZoneRules_UTC___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_ZoneRules_UTC___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_ZoneRules_UTC___closed__2_value;
static lean_once_cell_t l_Std_Time_TimeZone_ZoneRules_UTC___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_ZoneRules_UTC___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_UTC;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorIdx(uint8_t v_x_1_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Std_Time_TimeZone_UTLocal_ctorIdx(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Std_Time_TimeZone_UTLocal_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(lean_object* v_ut_22_){
_start:
{
lean_inc(v_ut_22_);
return v_ut_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___redArg___boxed(lean_object* v_ut_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(v_ut_23_);
lean_dec(v_ut_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_ut_28_){
_start:
{
lean_inc(v_ut_28_);
return v_ut_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_ut_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Std_Time_TimeZone_UTLocal_ut_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_ut_32_);
lean_dec(v_ut_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___redArg(lean_object* v_local_35_){
_start:
{
lean_inc(v_local_35_);
return v_local_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___redArg___boxed(lean_object* v_local_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_Time_TimeZone_UTLocal_local_elim___redArg(v_local_36_);
lean_dec(v_local_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_local_41_){
_start:
{
lean_inc(v_local_41_);
return v_local_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_local_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Std_Time_TimeZone_UTLocal_local_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_local_45_);
lean_dec(v_local_45_);
return v_res_47_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(2u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_to_int(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr(uint8_t v_x_58_, lean_object* v_prec_59_){
_start:
{
lean_object* v___y_61_; lean_object* v___y_68_; 
if (v_x_58_ == 0)
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1024u);
v___x_75_ = lean_nat_dec_le(v___x_74_, v_prec_59_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_61_ = v___x_76_;
goto v___jp_60_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_61_ = v___x_77_;
goto v___jp_60_;
}
}
else
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_59_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_68_ = v___x_80_;
goto v___jp_67_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_62_ = ((lean_object*)(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1));
lean_inc(v___y_61_);
v___x_63_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_63_, 0, v___y_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = 0;
v___x_65_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set_uint8(v___x_65_, sizeof(void*)*1, v___x_64_);
v___x_66_ = l_Repr_addAppParen(v___x_65_, v_prec_59_);
return v___x_66_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_69_ = ((lean_object*)(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3));
lean_inc(v___y_68_);
v___x_70_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_70_, 0, v___y_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = 0;
v___x_72_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set_uint8(v___x_72_, sizeof(void*)*1, v___x_71_);
v___x_73_ = l_Repr_addAppParen(v___x_72_, v_prec_59_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___boxed(lean_object* v_x_82_, lean_object* v_prec_83_){
_start:
{
uint8_t v_x_117__boxed_84_; lean_object* v_res_85_; 
v_x_117__boxed_84_ = lean_unbox(v_x_82_);
v_res_85_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_x_117__boxed_84_, v_prec_83_);
lean_dec(v_prec_83_);
return v_res_85_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_instInhabitedUTLocal_default(void){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_instInhabitedUTLocal(void){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx(uint8_t v_x_90_){
_start:
{
if (v_x_90_ == 0)
{
lean_object* v___x_91_; 
v___x_91_ = lean_unsigned_to_nat(0u);
return v___x_91_;
}
else
{
lean_object* v___x_92_; 
v___x_92_ = lean_unsigned_to_nat(1u);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx___boxed(lean_object* v_x_93_){
_start:
{
uint8_t v_x_boxed_94_; lean_object* v_res_95_; 
v_x_boxed_94_ = lean_unbox(v_x_93_);
v_res_95_ = l_Std_Time_TimeZone_StdWall_ctorIdx(v_x_boxed_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___redArg(lean_object* v_k_96_){
_start:
{
lean_inc(v_k_96_);
return v_k_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___redArg___boxed(lean_object* v_k_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_Time_TimeZone_StdWall_ctorElim___redArg(v_k_97_);
lean_dec(v_k_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim(lean_object* v_motive_99_, lean_object* v_ctorIdx_100_, uint8_t v_t_101_, lean_object* v_h_102_, lean_object* v_k_103_){
_start:
{
lean_inc(v_k_103_);
return v_k_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___boxed(lean_object* v_motive_104_, lean_object* v_ctorIdx_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_k_108_){
_start:
{
uint8_t v_t_boxed_109_; lean_object* v_res_110_; 
v_t_boxed_109_ = lean_unbox(v_t_106_);
v_res_110_ = l_Std_Time_TimeZone_StdWall_ctorElim(v_motive_104_, v_ctorIdx_105_, v_t_boxed_109_, v_h_107_, v_k_108_);
lean_dec(v_k_108_);
lean_dec(v_ctorIdx_105_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___redArg(lean_object* v_wall_111_){
_start:
{
lean_inc(v_wall_111_);
return v_wall_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___redArg___boxed(lean_object* v_wall_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Time_TimeZone_StdWall_wall_elim___redArg(v_wall_112_);
lean_dec(v_wall_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim(lean_object* v_motive_114_, uint8_t v_t_115_, lean_object* v_h_116_, lean_object* v_wall_117_){
_start:
{
lean_inc(v_wall_117_);
return v_wall_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___boxed(lean_object* v_motive_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_wall_121_){
_start:
{
uint8_t v_t_boxed_122_; lean_object* v_res_123_; 
v_t_boxed_122_ = lean_unbox(v_t_119_);
v_res_123_ = l_Std_Time_TimeZone_StdWall_wall_elim(v_motive_118_, v_t_boxed_122_, v_h_120_, v_wall_121_);
lean_dec(v_wall_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___redArg(lean_object* v_standard_124_){
_start:
{
lean_inc(v_standard_124_);
return v_standard_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___redArg___boxed(lean_object* v_standard_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_Time_TimeZone_StdWall_standard_elim___redArg(v_standard_125_);
lean_dec(v_standard_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim(lean_object* v_motive_127_, uint8_t v_t_128_, lean_object* v_h_129_, lean_object* v_standard_130_){
_start:
{
lean_inc(v_standard_130_);
return v_standard_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___boxed(lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_standard_134_){
_start:
{
uint8_t v_t_boxed_135_; lean_object* v_res_136_; 
v_t_boxed_135_ = lean_unbox(v_t_132_);
v_res_136_ = l_Std_Time_TimeZone_StdWall_standard_elim(v_motive_131_, v_t_boxed_135_, v_h_133_, v_standard_134_);
lean_dec(v_standard_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprStdWall_repr(uint8_t v_x_143_, lean_object* v_prec_144_){
_start:
{
lean_object* v___y_146_; lean_object* v___y_153_; 
if (v_x_143_ == 0)
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1024u);
v___x_160_ = lean_nat_dec_le(v___x_159_, v_prec_144_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_146_ = v___x_161_;
goto v___jp_145_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_146_ = v___x_162_;
goto v___jp_145_;
}
}
else
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(1024u);
v___x_164_ = lean_nat_dec_le(v___x_163_, v_prec_144_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
v___x_165_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_153_ = v___x_165_;
goto v___jp_152_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_153_ = v___x_166_;
goto v___jp_152_;
}
}
v___jp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_147_ = ((lean_object*)(l_Std_Time_TimeZone_instReprStdWall_repr___closed__1));
lean_inc(v___y_146_);
v___x_148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_148_, 0, v___y_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = 0;
v___x_150_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*1, v___x_149_);
v___x_151_ = l_Repr_addAppParen(v___x_150_, v_prec_144_);
return v___x_151_;
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_154_ = ((lean_object*)(l_Std_Time_TimeZone_instReprStdWall_repr___closed__3));
lean_inc(v___y_153_);
v___x_155_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_155_, 0, v___y_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = 0;
v___x_157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*1, v___x_156_);
v___x_158_ = l_Repr_addAppParen(v___x_157_, v_prec_144_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprStdWall_repr___boxed(lean_object* v_x_167_, lean_object* v_prec_168_){
_start:
{
uint8_t v_x_113__boxed_169_; lean_object* v_res_170_; 
v_x_113__boxed_169_ = lean_unbox(v_x_167_);
v_res_170_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_x_113__boxed_169_, v_prec_168_);
lean_dec(v_prec_168_);
return v_res_170_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_instInhabitedStdWall_default(void){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_instInhabitedStdWall(void){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = 0;
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instReprLocalTimeType_repr_spec__0(lean_object* v_a_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_nat_to_int(v_a_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(13u);
v___x_191_ = lean_nat_to_int(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(9u);
v___x_199_ = lean_nat_to_int(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(16u);
v___x_204_ = lean_nat_to_int(v___x_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(8u);
v___x_209_ = lean_nat_to_int(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(11u);
v___x_214_ = lean_nat_to_int(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(14u);
v___x_219_ = lean_nat_to_int(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0));
v___x_222_ = lean_string_length(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26);
v___x_224_ = lean_nat_to_int(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(lean_object* v_x_229_){
_start:
{
lean_object* v_gmtOffset_230_; uint8_t v_isDst_231_; lean_object* v_abbreviation_232_; uint8_t v_wall_233_; uint8_t v_utLocal_234_; lean_object* v_identifier_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_gmtOffset_230_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_gmtOffset_230_);
v_isDst_231_ = lean_ctor_get_uint8(v_x_229_, sizeof(void*)*3);
v_abbreviation_232_ = lean_ctor_get(v_x_229_, 1);
lean_inc_ref(v_abbreviation_232_);
v_wall_233_ = lean_ctor_get_uint8(v_x_229_, sizeof(void*)*3 + 1);
v_utLocal_234_ = lean_ctor_get_uint8(v_x_229_, sizeof(void*)*3 + 2);
v_identifier_235_ = lean_ctor_get(v_x_229_, 2);
lean_inc_ref(v_identifier_235_);
lean_dec_ref(v_x_229_);
v___x_236_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5));
v___x_237_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6));
v___x_238_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_gmtOffset_230_);
lean_dec(v_gmtOffset_230_);
v___x_241_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = 0;
v___x_243_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_242_);
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_237_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9));
v___x_246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_box(1);
v___x_248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11));
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_236_);
v___x_252_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12);
v___x_253_ = l_Bool_repr___redArg(v_isDst_231_);
v___x_254_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_242_);
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_251_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___x_245_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_247_);
v___x_259_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14));
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_236_);
v___x_262_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15);
v___x_263_ = l_String_quote(v_abbreviation_232_);
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
v___x_265_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_262_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*1, v___x_242_);
v___x_267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_261_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_245_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_247_);
v___x_270_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17));
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_236_);
v___x_273_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18);
v___x_274_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_wall_233_, v___x_239_);
v___x_275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_242_);
v___x_277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_272_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_245_);
v___x_279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_247_);
v___x_280_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20));
v___x_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_236_);
v___x_283_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21);
v___x_284_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_utLocal_234_, v___x_239_);
v___x_285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*1, v___x_242_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_282_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_245_);
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_247_);
v___x_290_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23));
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_236_);
v___x_293_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24);
v___x_294_ = l_String_quote(v_identifier_235_);
v___x_295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
v___x_296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_293_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1, v___x_242_);
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_292_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27);
v___x_300_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28));
v___x_301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_298_);
v___x_302_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29));
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_301_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_299_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*1, v___x_242_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr(lean_object* v_x_306_, lean_object* v_prec_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_x_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___boxed(lean_object* v_x_309_, lean_object* v_prec_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr(v_x_309_, v_prec_310_);
lean_dec(v_prec_310_);
return v_res_311_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_nat_to_int(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2(void){
_start:
{
uint8_t v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_317_ = 0;
v___x_318_ = 0;
v___x_319_ = ((lean_object*)(l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1));
v___x_320_ = 0;
v___x_321_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_322_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_319_);
lean_ctor_set(v___x_322_, 2, v___x_319_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*3, v___x_320_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*3 + 1, v___x_318_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*3 + 2, v___x_317_);
return v___x_322_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default(void){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instInhabitedLocalTimeType_default_spec__0(lean_object* v_a_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_nat_to_int(v_a_324_);
v___x_326_ = l_Rat_ofInt(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object* v_time_328_){
_start:
{
lean_object* v_gmtOffset_329_; uint8_t v_isDst_330_; lean_object* v_abbreviation_331_; lean_object* v_identifier_332_; lean_object* v___x_333_; 
v_gmtOffset_329_ = lean_ctor_get(v_time_328_, 0);
v_isDst_330_ = lean_ctor_get_uint8(v_time_328_, sizeof(void*)*3);
v_abbreviation_331_ = lean_ctor_get(v_time_328_, 1);
v_identifier_332_ = lean_ctor_get(v_time_328_, 2);
lean_inc_ref(v_abbreviation_331_);
lean_inc_ref(v_identifier_332_);
lean_inc(v_gmtOffset_329_);
v___x_333_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_333_, 0, v_gmtOffset_329_);
lean_ctor_set(v___x_333_, 1, v_identifier_332_);
lean_ctor_set(v___x_333_, 2, v_abbreviation_331_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*3, v_isDst_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone___boxed(lean_object* v_time_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_time_334_);
lean_dec_ref(v_time_334_);
return v_res_335_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(17u);
v___x_349_ = lean_nat_to_int(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg(lean_object* v_x_350_){
_start:
{
lean_object* v_time_351_; lean_object* v_localTimeType_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_386_; 
v_time_351_ = lean_ctor_get(v_x_350_, 0);
v_localTimeType_352_ = lean_ctor_get(v_x_350_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_386_ == 0)
{
v___x_354_ = v_x_350_;
v_isShared_355_ = v_isSharedCheck_386_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_localTimeType_352_);
lean_inc(v_time_351_);
lean_dec(v_x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_386_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_356_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5));
v___x_357_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3));
v___x_358_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = l_Std_Time_Second_instReprOffset___lam__0(v_time_351_, v___x_359_);
lean_dec(v_time_351_);
if (v_isShared_355_ == 0)
{
lean_ctor_set_tag(v___x_354_, 4);
lean_ctor_set(v___x_354_, 1, v___x_360_);
lean_ctor_set(v___x_354_, 0, v___x_358_);
v___x_362_ = v___x_354_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_360_);
v___x_362_ = v_reuseFailAlloc_385_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_363_ = 0;
v___x_364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*1, v___x_363_);
v___x_365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_357_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9));
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = lean_box(1);
v___x_369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5));
v___x_371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_356_);
v___x_373_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6, &l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6_once, _init_l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6);
v___x_374_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_localTimeType_352_);
v___x_375_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*1, v___x_363_);
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_372_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27);
v___x_379_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28));
v___x_380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v___x_377_);
v___x_381_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29));
v___x_382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_378_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*1, v___x_363_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr(lean_object* v_x_387_, lean_object* v_prec_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_x_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr___boxed(lean_object* v_x_390_, lean_object* v_prec_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Time_TimeZone_instReprTransition_repr(v_x_390_, v_prec_391_);
lean_dec(v_prec_391_);
return v_res_392_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_395_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v___x_397_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0, &l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition_default(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1, &l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1_once, _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1);
return v___x_399_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Std_Time_TimeZone_instInhabitedTransition_default;
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
lean_object* v___x_409_; 
v___x_409_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__1));
return v___x_409_;
}
else
{
lean_object* v_val_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_val_410_ = lean_ctor_get(v_x_407_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v_x_407_, 1);
v___x_411_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__3));
v___x_412_ = l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(v_val_410_);
v___x_413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
v___x_414_ = l_Repr_addAppParen(v___x_413_, v_x_408_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___boxed(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(v_x_415_, v_x_416_);
lean_dec(v_x_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
if (lean_obj_tag(v_x_420_) == 0)
{
lean_dec(v_x_418_);
return v_x_419_;
}
else
{
lean_object* v_head_421_; lean_object* v_tail_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_432_; 
v_head_421_ = lean_ctor_get(v_x_420_, 0);
v_tail_422_ = lean_ctor_get(v_x_420_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_420_);
if (v_isSharedCheck_432_ == 0)
{
v___x_424_ = v_x_420_;
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_tail_422_);
lean_inc(v_head_421_);
lean_dec(v_x_420_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
lean_inc(v_x_418_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 5);
lean_ctor_set(v___x_424_, 1, v_x_418_);
lean_ctor_set(v___x_424_, 0, v_x_419_);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_x_419_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_x_418_);
v___x_427_ = v_reuseFailAlloc_431_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_421_);
v___x_429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v_x_419_ = v___x_429_;
v_x_420_ = v_tail_422_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
if (lean_obj_tag(v_x_435_) == 0)
{
lean_dec(v_x_433_);
return v_x_434_;
}
else
{
lean_object* v_head_436_; lean_object* v_tail_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_447_; 
v_head_436_ = lean_ctor_get(v_x_435_, 0);
v_tail_437_ = lean_ctor_get(v_x_435_, 1);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_435_);
if (v_isSharedCheck_447_ == 0)
{
v___x_439_ = v_x_435_;
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_tail_437_);
lean_inc(v_head_436_);
lean_dec(v_x_435_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
lean_inc(v_x_433_);
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 5);
lean_ctor_set(v___x_439_, 1, v_x_433_);
lean_ctor_set(v___x_439_, 0, v_x_434_);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_x_434_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_x_433_);
v___x_442_ = v_reuseFailAlloc_446_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_436_);
v___x_444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(v_x_433_, v___x_444_, v_tail_437_);
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v___x_450_; 
lean_dec(v_x_449_);
v___x_450_ = lean_box(0);
return v___x_450_;
}
else
{
lean_object* v_tail_451_; 
v_tail_451_ = lean_ctor_get(v_x_448_, 1);
if (lean_obj_tag(v_tail_451_) == 0)
{
lean_object* v_head_452_; lean_object* v___x_453_; 
lean_dec(v_x_449_);
v_head_452_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_head_452_);
lean_dec_ref_known(v_x_448_, 2);
v___x_453_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_452_);
return v___x_453_;
}
else
{
lean_object* v_head_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_inc(v_tail_451_);
v_head_454_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_head_454_);
lean_dec_ref_known(v_x_448_, 2);
v___x_455_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_454_);
v___x_456_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(v_x_449_, v___x_455_, v_tail_451_);
return v___x_456_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0));
v___x_463_ = lean_string_length(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3);
v___x_465_ = lean_nat_to_int(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(lean_object* v_xs_473_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_array_get_size(v_xs_473_);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_nat_dec_eq(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_477_ = lean_array_to_list(v_xs_473_);
v___x_478_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1));
v___x_479_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(v___x_477_, v___x_478_);
v___x_480_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4);
v___x_481_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5));
v___x_482_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_479_);
v___x_483_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6));
v___x_484_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_480_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Std_Format_fill(v___x_485_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; 
lean_dec_ref(v_xs_473_);
v___x_487_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8));
return v___x_487_;
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(24u);
v___x_498_ = lean_nat_to_int(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(15u);
v___x_503_ = lean_nat_to_int(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(18u);
v___x_508_ = lean_nat_to_int(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(lean_object* v_x_509_){
_start:
{
lean_object* v_initialLocalTimeType_510_; lean_object* v_transitions_511_; lean_object* v_transitionRule_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_initialLocalTimeType_510_ = lean_ctor_get(v_x_509_, 0);
lean_inc_ref(v_initialLocalTimeType_510_);
v_transitions_511_ = lean_ctor_get(v_x_509_, 1);
lean_inc_ref(v_transitions_511_);
v_transitionRule_512_ = lean_ctor_get(v_x_509_, 2);
lean_inc(v_transitionRule_512_);
lean_dec_ref(v_x_509_);
v___x_513_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5));
v___x_514_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3));
v___x_515_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_initialLocalTimeType_510_);
v___x_518_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_515_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = 0;
v___x_520_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*1, v___x_519_);
v___x_521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_514_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9));
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_box(1);
v___x_525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6));
v___x_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_513_);
v___x_529_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7);
v___x_530_ = l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(v_transitions_511_);
v___x_531_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set_uint8(v___x_532_, sizeof(void*)*1, v___x_519_);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_528_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_522_);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_524_);
v___x_536_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__9));
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_513_);
v___x_539_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10);
v___x_540_ = l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(v_transitionRule_512_, v___x_516_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_519_);
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_538_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27);
v___x_545_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28));
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_543_);
v___x_547_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29));
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_544_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set_uint8(v___x_550_, sizeof(void*)*1, v___x_519_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr(lean_object* v_x_551_, lean_object* v_prec_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(v_x_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___boxed(lean_object* v_x_554_, lean_object* v_prec_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_Time_TimeZone_instReprZoneRules_repr(v_x_554_, v_prec_555_);
lean_dec(v_prec_555_);
return v_res_556_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_561_ = lean_box(0);
v___x_562_ = ((lean_object*)(l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0));
v___x_563_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v___x_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
lean_ctor_set(v___x_564_, 2, v___x_561_);
return v___x_564_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default(void){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1, &l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1_once, _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1);
return v___x_565_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules(void){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timestamp(lean_object* v_t_567_){
_start:
{
lean_object* v_time_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_time_568_ = lean_ctor_get(v_t_567_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_t_567_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_t_567_, 1);
lean_dec(v_unused_577_);
v___x_570_ = v_t_567_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_time_568_);
lean_dec(v_t_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_572_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_time_568_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_572_);
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(lean_object* v_transition_578_){
_start:
{
lean_object* v_localTimeType_579_; lean_object* v_gmtOffset_580_; uint8_t v_isDst_581_; lean_object* v_abbreviation_582_; lean_object* v_identifier_583_; lean_object* v___x_584_; 
v_localTimeType_579_ = lean_ctor_get(v_transition_578_, 1);
v_gmtOffset_580_ = lean_ctor_get(v_localTimeType_579_, 0);
v_isDst_581_ = lean_ctor_get_uint8(v_localTimeType_579_, sizeof(void*)*3);
v_abbreviation_582_ = lean_ctor_get(v_localTimeType_579_, 1);
v_identifier_583_ = lean_ctor_get(v_localTimeType_579_, 2);
lean_inc_ref(v_abbreviation_582_);
lean_inc_ref(v_identifier_583_);
lean_inc(v_gmtOffset_580_);
v___x_584_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_584_, 0, v_gmtOffset_580_);
lean_ctor_set(v___x_584_, 1, v_identifier_583_);
lean_ctor_set(v___x_584_, 2, v_abbreviation_582_);
lean_ctor_set_uint8(v___x_584_, sizeof(void*)*3, v_isDst_581_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition___boxed(lean_object* v_transition_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_transition_585_);
lean_dec_ref(v_transition_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(lean_object* v_value_587_, lean_object* v_as_588_, lean_object* v_j_589_){
_start:
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = lean_array_get_size(v_as_588_);
v___x_591_ = lean_nat_dec_lt(v_j_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
lean_dec(v_j_589_);
v___x_592_ = lean_box(0);
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v_time_594_; uint8_t v___x_595_; 
v___x_593_ = lean_array_fget_borrowed(v_as_588_, v_j_589_);
v_time_594_ = lean_ctor_get(v___x_593_, 0);
v___x_595_ = lean_int_dec_lt(v_value_587_, v_time_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_j_589_, v___x_596_);
lean_dec(v_j_589_);
v_j_589_ = v___x_597_;
goto _start;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v_j_589_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0___boxed(lean_object* v_value_600_, lean_object* v_as_601_, lean_object* v_j_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_value_600_, v_as_601_, v_j_602_);
lean_dec_ref(v_as_601_);
lean_dec(v_value_600_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(lean_object* v_transitions_604_, lean_object* v_timestamp_605_){
_start:
{
lean_object* v_second_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_second_606_ = lean_ctor_get(v_timestamp_605_, 0);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_second_606_, v_transitions_604_, v___x_607_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_array_get_size(v_transitions_604_);
v___x_610_ = lean_nat_dec_eq(v___x_609_, v___x_607_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_nat_sub(v___x_609_, v___x_611_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
else
{
return v___x_608_;
}
}
else
{
lean_object* v_val_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_625_; 
v_val_614_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_625_ == 0)
{
v___x_616_ = v___x_608_;
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_val_614_);
lean_dec(v___x_608_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_eq(v_val_614_, v___x_607_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_sub(v_val_614_, v___x_619_);
lean_dec(v_val_614_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_620_);
v___x_622_ = v___x_616_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
else
{
lean_object* v___x_624_; 
lean_del_object(v___x_616_);
lean_dec(v_val_614_);
v___x_624_ = lean_box(0);
return v___x_624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp___boxed(lean_object* v_transitions_626_, lean_object* v_timestamp_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_626_, v_timestamp_627_);
lean_dec_ref(v_timestamp_627_);
lean_dec_ref(v_transitions_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object* v_transitions_629_, lean_object* v_timestamp_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_629_, v_timestamp_630_);
if (lean_obj_tag(v___x_631_) == 1)
{
lean_object* v_val_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_643_; 
v_val_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_643_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_643_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_val_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_643_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_array_get_size(v_transitions_629_);
v___x_637_ = lean_nat_dec_lt(v_val_632_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_del_object(v___x_634_);
lean_dec(v_val_632_);
v___x_638_ = lean_box(0);
return v___x_638_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_array_fget_borrowed(v_transitions_629_, v_val_632_);
lean_dec(v_val_632_);
lean_inc(v___x_639_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_639_);
v___x_641_ = v___x_634_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_object* v___x_644_; 
lean_dec(v___x_631_);
v___x_644_ = lean_box(0);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp___boxed(lean_object* v_transitions_645_, lean_object* v_timestamp_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_645_, v_timestamp_646_);
lean_dec_ref(v_timestamp_646_);
lean_dec_ref(v_transitions_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object* v_transitions_651_, lean_object* v_tm_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_651_, v_tm_652_);
if (lean_obj_tag(v___x_653_) == 1)
{
lean_object* v_val_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_662_; 
v_val_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_662_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_val_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_662_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_val_654_);
lean_dec(v_val_654_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v___x_663_; 
lean_dec(v___x_653_);
v___x_663_ = ((lean_object*)(l_Std_Time_TimeZone_Transition_timezoneAt___closed__1));
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt___boxed(lean_object* v_transitions_664_, lean_object* v_tm_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_664_, v_tm_665_);
lean_dec_ref(v_tm_665_);
lean_dec_ref(v_transitions_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds_spec__0(lean_object* v_a_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Rat_ofInt(v_a_667_);
return v___x_668_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(86400u);
v___x_670_ = lean_nat_to_int(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(lean_object* v_rule_671_, lean_object* v_year_672_, lean_object* v_wallOffset_673_){
_start:
{
lean_object* v_spec_674_; lean_object* v_time_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_spec_674_ = lean_ctor_get(v_rule_671_, 0);
lean_inc_ref(v_spec_674_);
v_time_675_ = lean_ctor_get(v_rule_671_, 1);
lean_inc(v_time_675_);
lean_dec_ref(v_rule_671_);
v___x_676_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDay(v_spec_674_, v_year_672_);
v___x_677_ = lean_obj_once(&l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0, &l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once, _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0);
v___x_678_ = lean_int_mul(v___x_676_, v___x_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_int_add(v___x_678_, v_time_675_);
lean_dec(v_time_675_);
lean_dec(v___x_678_);
v___x_680_ = lean_int_sub(v___x_679_, v_wallOffset_673_);
lean_dec(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___boxed(lean_object* v_rule_681_, lean_object* v_year_682_, lean_object* v_wallOffset_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_rule_681_, v_year_682_, v_wallOffset_683_);
lean_dec(v_wallOffset_683_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt(lean_object* v_rule_685_, lean_object* v_tm_686_){
_start:
{
lean_object* v_stdName_687_; lean_object* v_stdOffset_688_; lean_object* v_dst_689_; uint8_t v___x_690_; lean_object* v_stdTz_691_; 
v_stdName_687_ = lean_ctor_get(v_rule_685_, 0);
lean_inc_ref_n(v_stdName_687_, 2);
v_stdOffset_688_ = lean_ctor_get(v_rule_685_, 1);
lean_inc_n(v_stdOffset_688_, 2);
v_dst_689_ = lean_ctor_get(v_rule_685_, 2);
lean_inc(v_dst_689_);
lean_dec_ref(v_rule_685_);
v___x_690_ = 0;
v_stdTz_691_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_stdTz_691_, 0, v_stdOffset_688_);
lean_ctor_set(v_stdTz_691_, 1, v_stdName_687_);
lean_ctor_set(v_stdTz_691_, 2, v_stdName_687_);
lean_ctor_set_uint8(v_stdTz_691_, sizeof(void*)*3, v___x_690_);
if (lean_obj_tag(v_dst_689_) == 1)
{
lean_object* v_val_692_; lean_object* v_name_693_; lean_object* v_offset_694_; lean_object* v_start_695_; lean_object* v_end___696_; uint8_t v___x_697_; lean_object* v_dstTz_698_; 
v_val_692_ = lean_ctor_get(v_dst_689_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v_dst_689_, 1);
v_name_693_ = lean_ctor_get(v_val_692_, 0);
lean_inc_ref_n(v_name_693_, 2);
v_offset_694_ = lean_ctor_get(v_val_692_, 1);
lean_inc_n(v_offset_694_, 2);
v_start_695_ = lean_ctor_get(v_val_692_, 2);
lean_inc(v_start_695_);
v_end___696_ = lean_ctor_get(v_val_692_, 3);
lean_inc(v_end___696_);
lean_dec(v_val_692_);
v___x_697_ = 1;
v_dstTz_698_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_dstTz_698_, 0, v_offset_694_);
lean_ctor_set(v_dstTz_698_, 1, v_name_693_);
lean_ctor_set(v_dstTz_698_, 2, v_name_693_);
lean_ctor_set_uint8(v_dstTz_698_, sizeof(void*)*3, v___x_697_);
if (lean_obj_tag(v_start_695_) == 1)
{
if (lean_obj_tag(v_end___696_) == 1)
{
lean_object* v_val_699_; lean_object* v_val_700_; lean_object* v_second_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_year_705_; lean_object* v_dstStart_706_; lean_object* v_dstEnd_707_; uint8_t v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; 
v_val_699_ = lean_ctor_get(v_start_695_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v_start_695_, 1);
v_val_700_ = lean_ctor_get(v_end___696_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_end___696_, 1);
v_second_701_ = lean_ctor_get(v_tm_686_, 0);
v___x_702_ = lean_obj_once(&l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0, &l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once, _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0);
v___x_703_ = lean_int_ediv(v_second_701_, v___x_702_);
v___x_704_ = l_Std_Time_PlainDate_ofEpochDay(v___x_703_);
lean_dec(v___x_703_);
v_year_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc_n(v_year_705_, 2);
lean_dec_ref(v___x_704_);
v_dstStart_706_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_val_699_, v_year_705_, v_stdOffset_688_);
lean_dec(v_stdOffset_688_);
v_dstEnd_707_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_val_700_, v_year_705_, v_offset_694_);
lean_dec(v_offset_694_);
v___x_708_ = lean_int_dec_le(v_dstStart_706_, v_dstEnd_707_);
v___x_709_ = lean_int_dec_le(v_dstStart_706_, v_second_701_);
lean_dec(v_dstStart_706_);
v___x_710_ = lean_int_dec_lt(v_second_701_, v_dstEnd_707_);
lean_dec(v_dstEnd_707_);
if (v___x_708_ == 0)
{
if (v___x_710_ == 0)
{
if (v___x_709_ == 0)
{
lean_dec_ref_known(v_dstTz_698_, 3);
return v_stdTz_691_;
}
else
{
lean_dec_ref_known(v_stdTz_691_, 3);
return v_dstTz_698_;
}
}
else
{
lean_dec_ref_known(v_stdTz_691_, 3);
return v_dstTz_698_;
}
}
else
{
if (v___x_709_ == 0)
{
lean_dec_ref_known(v_dstTz_698_, 3);
return v_stdTz_691_;
}
else
{
if (v___x_710_ == 0)
{
lean_dec_ref_known(v_dstTz_698_, 3);
return v_stdTz_691_;
}
else
{
lean_dec_ref_known(v_stdTz_691_, 3);
return v_dstTz_698_;
}
}
}
}
else
{
lean_dec_ref_known(v_start_695_, 1);
lean_dec_ref_known(v_dstTz_698_, 3);
lean_dec(v_end___696_);
lean_dec(v_offset_694_);
lean_dec(v_stdOffset_688_);
return v_stdTz_691_;
}
}
else
{
lean_dec_ref_known(v_dstTz_698_, 3);
lean_dec(v_end___696_);
lean_dec(v_start_695_);
lean_dec(v_offset_694_);
lean_dec(v_stdOffset_688_);
return v_stdTz_691_;
}
}
else
{
lean_dec(v_dst_689_);
lean_dec(v_stdOffset_688_);
return v_stdTz_691_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt___boxed(lean_object* v_rule_711_, lean_object* v_tm_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_rule_711_, v_tm_712_);
lean_dec_ref(v_tm_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(lean_object* v_second_714_, lean_object* v_00___715_){
_start:
{
uint8_t v___x_716_; lean_object* v___x_717_; 
v___x_716_ = 1;
v___x_717_ = l_Std_Time_TimeZone_Offset_toIsoString(v_second_714_, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object* v_second_720_, lean_object* v_identifier_721_, lean_object* v_abbreviation_722_){
_start:
{
uint8_t v___x_723_; uint8_t v___y_725_; uint8_t v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_734_; 
v___x_723_ = 0;
if (lean_obj_tag(v_abbreviation_722_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_box(0);
lean_inc(v_second_720_);
v___x_741_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(v_second_720_, v___x_740_);
v___y_734_ = v___x_741_;
goto v___jp_733_;
}
else
{
lean_object* v_val_742_; 
v_val_742_ = lean_ctor_get(v_abbreviation_722_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v_abbreviation_722_, 1);
v___y_734_ = v_val_742_;
goto v___jp_733_;
}
v___jp_724_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_729_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_729_, 0, v_second_720_);
lean_ctor_set(v___x_729_, 1, v___y_727_);
lean_ctor_set(v___x_729_, 2, v___y_728_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*3, v___x_723_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*3 + 1, v___y_726_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*3 + 2, v___y_725_);
v___x_730_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0));
v___x_731_ = lean_box(0);
v___x_732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_732_, 0, v___x_729_);
lean_ctor_set(v___x_732_, 1, v___x_730_);
lean_ctor_set(v___x_732_, 2, v___x_731_);
return v___x_732_;
}
v___jp_733_:
{
uint8_t v___x_735_; uint8_t v___x_736_; 
v___x_735_ = 1;
v___x_736_ = 0;
if (lean_obj_tag(v_identifier_721_) == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_box(0);
lean_inc(v_second_720_);
v___x_738_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(v_second_720_, v___x_737_);
v___y_725_ = v___x_736_;
v___y_726_ = v___x_735_;
v___y_727_ = v___y_734_;
v___y_728_ = v___x_738_;
goto v___jp_724_;
}
else
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v_identifier_721_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v_identifier_721_, 1);
v___y_725_ = v___x_736_;
v___y_726_ = v___x_735_;
v___y_727_ = v___y_734_;
v___y_728_ = v_val_739_;
goto v___jp_724_;
}
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_nat_to_int(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_UTC___closed__2));
v___x_749_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_UTC___closed__0, &l_Std_Time_TimeZone_ZoneRules_UTC___closed__0_once, _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0);
v___x_750_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_749_, v___x_748_, v___x_748_);
return v___x_750_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_UTC___closed__3, &l_Std_Time_TimeZone_ZoneRules_UTC___closed__3_once, _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(lean_object* v_zr_752_, lean_object* v_timestamp_753_){
_start:
{
lean_object* v_initialLocalTimeType_754_; lean_object* v_transitions_755_; lean_object* v_transitionRule_756_; lean_object* v___x_757_; 
v_initialLocalTimeType_754_ = lean_ctor_get(v_zr_752_, 0);
lean_inc_ref(v_initialLocalTimeType_754_);
v_transitions_755_ = lean_ctor_get(v_zr_752_, 1);
lean_inc_ref(v_transitions_755_);
v_transitionRule_756_ = lean_ctor_get(v_zr_752_, 2);
lean_inc(v_transitionRule_756_);
lean_dec_ref(v_zr_752_);
v___x_757_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_755_, v_timestamp_753_);
if (lean_obj_tag(v___x_757_) == 1)
{
lean_object* v_val_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_val_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_val_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = lean_array_get_size(v_transitions_755_);
v___x_760_ = lean_nat_dec_lt(v_val_758_, v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v_val_758_);
lean_dec(v_transitionRule_756_);
lean_dec_ref(v_transitions_755_);
return v_initialLocalTimeType_754_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
lean_dec_ref(v_initialLocalTimeType_754_);
v___x_761_ = lean_array_fget(v_transitions_755_, v_val_758_);
lean_dec_ref(v_transitions_755_);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_val_758_, v___x_762_);
lean_dec(v_val_758_);
v___x_764_ = lean_nat_dec_eq(v___x_763_, v___x_759_);
lean_dec(v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v_localTimeType_765_; 
lean_dec(v_transitionRule_756_);
v_localTimeType_765_ = lean_ctor_get(v___x_761_, 1);
lean_inc_ref(v_localTimeType_765_);
lean_dec(v___x_761_);
return v_localTimeType_765_;
}
else
{
if (lean_obj_tag(v_transitionRule_756_) == 1)
{
lean_object* v_val_766_; lean_object* v_localTimeType_767_; lean_object* v_tz_768_; lean_object* v_offset_769_; lean_object* v_name_770_; lean_object* v_abbreviation_771_; uint8_t v_isDST_772_; uint8_t v_wall_773_; uint8_t v_utLocal_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_val_766_ = lean_ctor_get(v_transitionRule_756_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v_transitionRule_756_, 1);
v_localTimeType_767_ = lean_ctor_get(v___x_761_, 1);
lean_inc_ref(v_localTimeType_767_);
lean_dec(v___x_761_);
v_tz_768_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_val_766_, v_timestamp_753_);
v_offset_769_ = lean_ctor_get(v_tz_768_, 0);
lean_inc(v_offset_769_);
v_name_770_ = lean_ctor_get(v_tz_768_, 1);
lean_inc_ref(v_name_770_);
v_abbreviation_771_ = lean_ctor_get(v_tz_768_, 2);
lean_inc_ref(v_abbreviation_771_);
v_isDST_772_ = lean_ctor_get_uint8(v_tz_768_, sizeof(void*)*3);
lean_dec_ref(v_tz_768_);
v_wall_773_ = lean_ctor_get_uint8(v_localTimeType_767_, sizeof(void*)*3 + 1);
v_utLocal_774_ = lean_ctor_get_uint8(v_localTimeType_767_, sizeof(void*)*3 + 2);
v_isSharedCheck_781_ = !lean_is_exclusive(v_localTimeType_767_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_782_ = lean_ctor_get(v_localTimeType_767_, 2);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_localTimeType_767_, 1);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_localTimeType_767_, 0);
lean_dec(v_unused_784_);
v___x_776_ = v_localTimeType_767_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_dec(v_localTimeType_767_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 2, v_name_770_);
lean_ctor_set(v___x_776_, 1, v_abbreviation_771_);
lean_ctor_set(v___x_776_, 0, v_offset_769_);
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_offset_769_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_abbreviation_771_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v_name_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_780_, sizeof(void*)*3 + 1, v_wall_773_);
lean_ctor_set_uint8(v_reuseFailAlloc_780_, sizeof(void*)*3 + 2, v_utLocal_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*3, v_isDST_772_);
return v___x_779_;
}
}
}
else
{
lean_object* v_localTimeType_785_; 
lean_dec(v_transitionRule_756_);
v_localTimeType_785_ = lean_ctor_get(v___x_761_, 1);
lean_inc_ref(v_localTimeType_785_);
lean_dec(v___x_761_);
return v_localTimeType_785_;
}
}
}
}
else
{
lean_dec(v___x_757_);
lean_dec(v_transitionRule_756_);
lean_dec_ref(v_transitions_755_);
return v_initialLocalTimeType_754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp___boxed(lean_object* v_zr_786_, lean_object* v_timestamp_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_786_, v_timestamp_787_);
lean_dec_ref(v_timestamp_787_);
return v_res_788_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1000000000u);
v___x_790_ = lean_nat_to_int(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(lean_object* v_wallTime_791_, lean_object* v_as_792_, size_t v_sz_793_, size_t v_i_794_, lean_object* v_b_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_lt(v_i_794_, v_sz_793_);
if (v___x_796_ == 0)
{
return v_b_795_;
}
else
{
lean_object* v_snd_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_827_; 
v_snd_797_ = lean_ctor_get(v_b_795_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_b_795_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_b_795_, 0);
lean_dec(v_unused_828_);
v___x_799_ = v_b_795_;
v_isShared_800_ = v_isSharedCheck_827_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_snd_797_);
lean_dec(v_b_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_827_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_gmtOffset_801_; lean_object* v_a_802_; lean_object* v___x_803_; lean_object* v_second_804_; lean_object* v_nano_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_gmtOffset_801_ = lean_ctor_get(v_snd_797_, 0);
v_a_802_ = lean_array_uget_borrowed(v_as_792_, v_i_794_);
lean_inc(v_a_802_);
v___x_803_ = l_Std_Time_TimeZone_Transition_timestamp(v_a_802_);
v_second_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_second_804_);
v_nano_805_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_nano_805_);
lean_dec_ref(v___x_803_);
v___x_806_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_807_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0);
v___x_808_ = lean_int_mul(v_second_804_, v___x_807_);
lean_dec(v_second_804_);
v___x_809_ = lean_int_add(v___x_808_, v_nano_805_);
lean_dec(v_nano_805_);
lean_dec(v___x_808_);
v___x_810_ = lean_int_mul(v_gmtOffset_801_, v___x_807_);
v___x_811_ = lean_int_add(v___x_810_, v___x_806_);
lean_dec(v___x_810_);
v___x_812_ = lean_int_add(v___x_809_, v___x_811_);
lean_dec(v___x_811_);
lean_dec(v___x_809_);
v___x_813_ = l_Std_Time_Duration_ofNanoseconds(v___x_812_);
lean_dec(v___x_812_);
v___x_814_ = l_Std_Time_Duration_instDecidableLt(v_wallTime_791_, v___x_813_);
lean_dec_ref(v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v_localTimeType_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
lean_dec(v_snd_797_);
v_localTimeType_815_ = lean_ctor_get(v_a_802_, 1);
v___x_816_ = lean_box(0);
lean_inc_ref(v_localTimeType_815_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_localTimeType_815_);
lean_ctor_set(v___x_799_, 0, v___x_816_);
v___x_818_ = v___x_799_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_localTimeType_815_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
size_t v___x_819_; size_t v___x_820_; 
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_794_, v___x_819_);
v_i_794_ = v___x_820_;
v_b_795_ = v___x_818_;
goto _start;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_825_; 
lean_inc(v_snd_797_);
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_snd_797_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_823_);
v___x_825_ = v___x_799_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_snd_797_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___boxed(lean_object* v_wallTime_829_, lean_object* v_as_830_, lean_object* v_sz_831_, lean_object* v_i_832_, lean_object* v_b_833_){
_start:
{
size_t v_sz_boxed_834_; size_t v_i_boxed_835_; lean_object* v_res_836_; 
v_sz_boxed_834_ = lean_unbox_usize(v_sz_831_);
lean_dec(v_sz_831_);
v_i_boxed_835_ = lean_unbox_usize(v_i_832_);
lean_dec(v_i_832_);
v_res_836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_829_, v_as_830_, v_sz_boxed_834_, v_i_boxed_835_, v_b_833_);
lean_dec_ref(v_as_830_);
lean_dec_ref(v_wallTime_829_);
return v_res_836_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_838_ = lean_int_neg(v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object* v_zr_839_, lean_object* v_wallTime_840_){
_start:
{
lean_object* v_initialLocalTimeType_841_; lean_object* v_transitions_842_; lean_object* v_transitionRule_843_; lean_object* v___x_844_; lean_object* v___x_845_; size_t v_sz_846_; size_t v___x_847_; lean_object* v___x_848_; lean_object* v_fst_849_; 
v_initialLocalTimeType_841_ = lean_ctor_get(v_zr_839_, 0);
lean_inc_ref(v_initialLocalTimeType_841_);
v_transitions_842_ = lean_ctor_get(v_zr_839_, 1);
lean_inc_ref(v_transitions_842_);
v_transitionRule_843_ = lean_ctor_get(v_zr_839_, 2);
lean_inc(v_transitionRule_843_);
lean_dec_ref(v_zr_839_);
v___x_844_ = lean_box(0);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v_initialLocalTimeType_841_);
v_sz_846_ = lean_array_size(v_transitions_842_);
v___x_847_ = ((size_t)0ULL);
v___x_848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_840_, v_transitions_842_, v_sz_846_, v___x_847_, v___x_845_);
lean_dec_ref(v_transitions_842_);
v_fst_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_fst_849_);
if (lean_obj_tag(v_fst_849_) == 0)
{
if (lean_obj_tag(v_transitionRule_843_) == 1)
{
lean_object* v_snd_850_; lean_object* v_val_851_; lean_object* v_gmtOffset_852_; uint8_t v_wall_853_; uint8_t v_utLocal_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_877_; 
v_snd_850_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_snd_850_);
lean_dec_ref(v___x_848_);
v_val_851_ = lean_ctor_get(v_transitionRule_843_, 0);
lean_inc(v_val_851_);
lean_dec_ref_known(v_transitionRule_843_, 1);
v_gmtOffset_852_ = lean_ctor_get(v_snd_850_, 0);
v_wall_853_ = lean_ctor_get_uint8(v_snd_850_, sizeof(void*)*3 + 1);
v_utLocal_854_ = lean_ctor_get_uint8(v_snd_850_, sizeof(void*)*3 + 2);
v_isSharedCheck_877_ = !lean_is_exclusive(v_snd_850_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; lean_object* v_unused_879_; 
v_unused_878_ = lean_ctor_get(v_snd_850_, 2);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_snd_850_, 1);
lean_dec(v_unused_879_);
v___x_856_ = v_snd_850_;
v_isShared_857_ = v_isSharedCheck_877_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_gmtOffset_852_);
lean_dec(v_snd_850_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_877_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_second_858_; lean_object* v_nano_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v_offset_870_; lean_object* v_name_871_; lean_object* v_abbreviation_872_; uint8_t v_isDST_873_; lean_object* v___x_875_; 
v_second_858_ = lean_ctor_get(v_wallTime_840_, 0);
v_nano_859_ = lean_ctor_get(v_wallTime_840_, 1);
v___x_860_ = lean_int_neg(v_gmtOffset_852_);
lean_dec(v_gmtOffset_852_);
v___x_861_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0, &l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0_once, _init_l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0);
v___x_862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0);
v___x_863_ = lean_int_mul(v_second_858_, v___x_862_);
v___x_864_ = lean_int_add(v___x_863_, v_nano_859_);
lean_dec(v___x_863_);
v___x_865_ = lean_int_mul(v___x_860_, v___x_862_);
lean_dec(v___x_860_);
v___x_866_ = lean_int_add(v___x_865_, v___x_861_);
lean_dec(v___x_865_);
v___x_867_ = lean_int_add(v___x_864_, v___x_866_);
lean_dec(v___x_866_);
lean_dec(v___x_864_);
v___x_868_ = l_Std_Time_Duration_ofNanoseconds(v___x_867_);
lean_dec(v___x_867_);
v___x_869_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_val_851_, v___x_868_);
lean_dec_ref(v___x_868_);
v_offset_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_offset_870_);
v_name_871_ = lean_ctor_get(v___x_869_, 1);
lean_inc_ref(v_name_871_);
v_abbreviation_872_ = lean_ctor_get(v___x_869_, 2);
lean_inc_ref(v_abbreviation_872_);
v_isDST_873_ = lean_ctor_get_uint8(v___x_869_, sizeof(void*)*3);
lean_dec_ref(v___x_869_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 2, v_name_871_);
lean_ctor_set(v___x_856_, 1, v_abbreviation_872_);
lean_ctor_set(v___x_856_, 0, v_offset_870_);
v___x_875_ = v___x_856_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_offset_870_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_abbreviation_872_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_name_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*3 + 1, v_wall_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*3 + 2, v_utLocal_854_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*3, v_isDST_873_);
return v___x_875_;
}
}
}
else
{
lean_object* v_snd_880_; 
lean_dec(v_transitionRule_843_);
v_snd_880_ = lean_ctor_get(v___x_848_, 1);
lean_inc(v_snd_880_);
lean_dec_ref(v___x_848_);
return v_snd_880_;
}
}
else
{
lean_object* v_val_881_; 
lean_dec_ref(v___x_848_);
lean_dec(v_transitionRule_843_);
v_val_881_ = lean_ctor_get(v_fst_849_, 0);
lean_inc(v_val_881_);
lean_dec_ref_known(v_fst_849_, 1);
return v_val_881_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___boxed(lean_object* v_zr_882_, lean_object* v_wallTime_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_882_, v_wallTime_883_);
lean_dec_ref(v_wallTime_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object* v_zr_885_, lean_object* v_tm_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_885_, v_tm_886_);
v___x_888_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_887_);
lean_dec_ref(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt___boxed(lean_object* v_zr_889_, lean_object* v_tm_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_zr_889_, v_tm_890_);
lean_dec_ref(v_tm_890_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone(lean_object* v_tz_892_){
_start:
{
lean_object* v_offset_893_; lean_object* v_name_894_; lean_object* v_abbreviation_895_; uint8_t v_isDST_896_; uint8_t v___x_897_; uint8_t v___x_898_; lean_object* v_ltt_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_offset_893_ = lean_ctor_get(v_tz_892_, 0);
v_name_894_ = lean_ctor_get(v_tz_892_, 1);
v_abbreviation_895_ = lean_ctor_get(v_tz_892_, 2);
v_isDST_896_ = lean_ctor_get_uint8(v_tz_892_, sizeof(void*)*3);
v___x_897_ = 0;
v___x_898_ = 1;
lean_inc_ref(v_name_894_);
lean_inc_ref(v_abbreviation_895_);
lean_inc(v_offset_893_);
v_ltt_899_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_899_, 0, v_offset_893_);
lean_ctor_set(v_ltt_899_, 1, v_abbreviation_895_);
lean_ctor_set(v_ltt_899_, 2, v_name_894_);
lean_ctor_set_uint8(v_ltt_899_, sizeof(void*)*3, v_isDST_896_);
lean_ctor_set_uint8(v_ltt_899_, sizeof(void*)*3 + 1, v___x_897_);
lean_ctor_set_uint8(v_ltt_899_, sizeof(void*)*3 + 2, v___x_898_);
v___x_900_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0));
v___x_901_ = lean_box(0);
v___x_902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_902_, 0, v_ltt_899_);
lean_ctor_set(v___x_902_, 1, v___x_900_);
lean_ctor_set(v___x_902_, 2, v___x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone___boxed(lean_object* v_tz_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Std_Time_TimeZone_ZoneRules_ofTimeZone(v_tz_903_);
lean_dec_ref(v_tz_903_);
return v_res_904_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_RecurringRule(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_RecurringRule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_TimeZone_instInhabitedUTLocal_default = _init_l_Std_Time_TimeZone_instInhabitedUTLocal_default();
l_Std_Time_TimeZone_instInhabitedUTLocal = _init_l_Std_Time_TimeZone_instInhabitedUTLocal();
l_Std_Time_TimeZone_instInhabitedStdWall_default = _init_l_Std_Time_TimeZone_instInhabitedStdWall_default();
l_Std_Time_TimeZone_instInhabitedStdWall = _init_l_Std_Time_TimeZone_instInhabitedStdWall();
l_Std_Time_TimeZone_instInhabitedLocalTimeType_default = _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedLocalTimeType_default);
l_Std_Time_TimeZone_instInhabitedLocalTimeType = _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedLocalTimeType);
l_Std_Time_TimeZone_instInhabitedTransition_default = _init_l_Std_Time_TimeZone_instInhabitedTransition_default();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedTransition_default);
l_Std_Time_TimeZone_instInhabitedTransition = _init_l_Std_Time_TimeZone_instInhabitedTransition();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedTransition);
l_Std_Time_TimeZone_instInhabitedZoneRules_default = _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedZoneRules_default);
l_Std_Time_TimeZone_instInhabitedZoneRules = _init_l_Std_Time_TimeZone_instInhabitedZoneRules();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedZoneRules);
l_Std_Time_TimeZone_ZoneRules_UTC = _init_l_Std_Time_TimeZone_ZoneRules_UTC();
lean_mark_persistent(l_Std_Time_TimeZone_ZoneRules_UTC);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_RecurringRule(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_RecurringRule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_ZoneRules(builtin);
}
#ifdef __cplusplus
}
#endif
