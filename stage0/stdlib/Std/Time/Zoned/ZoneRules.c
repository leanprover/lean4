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
extern lean_object* l_Std_Time_Second_instInhabitedOffset;
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
uint8_t v_x_121__boxed_84_; lean_object* v_res_85_; 
v_x_121__boxed_84_ = lean_unbox(v_x_82_);
v_res_85_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_x_121__boxed_84_, v_prec_83_);
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
uint8_t v_x_117__boxed_169_; lean_object* v_res_170_; 
v_x_117__boxed_169_ = lean_unbox(v_x_167_);
v_res_170_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_x_117__boxed_169_, v_prec_168_);
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
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v___x_396_ = l_Std_Time_Second_instInhabitedOffset;
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
return v___x_397_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition_default(void){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0, &l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0);
return v___x_398_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_Time_TimeZone_instInhabitedTransition_default;
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v___x_408_; 
v___x_408_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__1));
return v___x_408_;
}
else
{
lean_object* v_val_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_val_409_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v_x_406_, 1);
v___x_410_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__3));
v___x_411_ = l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(v_val_409_);
v___x_412_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Repr_addAppParen(v___x_412_, v_x_407_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___boxed(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(v_x_414_, v_x_415_);
lean_dec(v_x_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_dec(v_x_417_);
return v_x_418_;
}
else
{
lean_object* v_head_420_; lean_object* v_tail_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
v_head_420_ = lean_ctor_get(v_x_419_, 0);
v_tail_421_ = lean_ctor_get(v_x_419_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_419_);
if (v_isSharedCheck_431_ == 0)
{
v___x_423_ = v_x_419_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_tail_421_);
lean_inc(v_head_420_);
lean_dec(v_x_419_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
lean_inc(v_x_417_);
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 5);
lean_ctor_set(v___x_423_, 1, v_x_417_);
lean_ctor_set(v___x_423_, 0, v_x_418_);
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_x_418_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_x_417_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_420_);
v___x_428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v_x_418_ = v___x_428_;
v_x_419_ = v_tail_421_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_dec(v_x_432_);
return v_x_433_;
}
else
{
lean_object* v_head_435_; lean_object* v_tail_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
v_head_435_ = lean_ctor_get(v_x_434_, 0);
v_tail_436_ = lean_ctor_get(v_x_434_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_446_ == 0)
{
v___x_438_ = v_x_434_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_tail_436_);
lean_inc(v_head_435_);
lean_dec(v_x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
lean_inc(v_x_432_);
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 5);
lean_ctor_set(v___x_438_, 1, v_x_432_);
lean_ctor_set(v___x_438_, 0, v_x_433_);
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_x_433_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_x_432_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_435_);
v___x_443_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
v___x_444_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(v_x_432_, v___x_443_, v_tail_436_);
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v___x_449_; 
lean_dec(v_x_448_);
v___x_449_ = lean_box(0);
return v___x_449_;
}
else
{
lean_object* v_tail_450_; 
v_tail_450_ = lean_ctor_get(v_x_447_, 1);
if (lean_obj_tag(v_tail_450_) == 0)
{
lean_object* v_head_451_; lean_object* v___x_452_; 
lean_dec(v_x_448_);
v_head_451_ = lean_ctor_get(v_x_447_, 0);
lean_inc(v_head_451_);
lean_dec_ref_known(v_x_447_, 2);
v___x_452_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_451_);
return v___x_452_;
}
else
{
lean_object* v_head_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
lean_inc(v_tail_450_);
v_head_453_ = lean_ctor_get(v_x_447_, 0);
lean_inc(v_head_453_);
lean_dec_ref_known(v_x_447_, 2);
v___x_454_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_453_);
v___x_455_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(v_x_448_, v___x_454_, v_tail_450_);
return v___x_455_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0));
v___x_462_ = lean_string_length(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3);
v___x_464_ = lean_nat_to_int(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(lean_object* v_xs_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = lean_array_get_size(v_xs_472_);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_nat_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_476_ = lean_array_to_list(v_xs_472_);
v___x_477_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1));
v___x_478_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(v___x_476_, v___x_477_);
v___x_479_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4);
v___x_480_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5));
v___x_481_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_478_);
v___x_482_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6));
v___x_483_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_479_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = l_Std_Format_fill(v___x_484_);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
lean_dec_ref(v_xs_472_);
v___x_486_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8));
return v___x_486_;
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(24u);
v___x_497_ = lean_nat_to_int(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(15u);
v___x_502_ = lean_nat_to_int(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(18u);
v___x_507_ = lean_nat_to_int(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(lean_object* v_x_508_){
_start:
{
lean_object* v_initialLocalTimeType_509_; lean_object* v_transitions_510_; lean_object* v_transitionRule_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_initialLocalTimeType_509_ = lean_ctor_get(v_x_508_, 0);
lean_inc_ref(v_initialLocalTimeType_509_);
v_transitions_510_ = lean_ctor_get(v_x_508_, 1);
lean_inc_ref(v_transitions_510_);
v_transitionRule_511_ = lean_ctor_get(v_x_508_, 2);
lean_inc(v_transitionRule_511_);
lean_dec_ref(v_x_508_);
v___x_512_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5));
v___x_513_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3));
v___x_514_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4);
v___x_515_ = lean_unsigned_to_nat(0u);
v___x_516_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_initialLocalTimeType_509_);
v___x_517_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_514_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = 0;
v___x_519_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*1, v___x_518_);
v___x_520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_513_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9));
v___x_522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = lean_box(1);
v___x_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6));
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_512_);
v___x_528_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7);
v___x_529_ = l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(v_transitions_510_);
v___x_530_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_518_);
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_527_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_521_);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set(v___x_534_, 1, v___x_523_);
v___x_535_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__9));
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_512_);
v___x_538_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10);
v___x_539_ = l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(v_transitionRule_511_, v___x_515_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*1, v___x_518_);
v___x_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_537_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27);
v___x_544_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28));
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_542_);
v___x_546_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29));
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_543_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*1, v___x_518_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr(lean_object* v_x_550_, lean_object* v_prec_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(v_x_550_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___boxed(lean_object* v_x_553_, lean_object* v_prec_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_Time_TimeZone_instReprZoneRules_repr(v_x_553_, v_prec_554_);
lean_dec(v_prec_554_);
return v_res_555_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = lean_box(0);
v___x_561_ = ((lean_object*)(l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0));
v___x_562_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v___x_563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v___x_561_);
lean_ctor_set(v___x_563_, 2, v___x_560_);
return v___x_563_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default(void){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1, &l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1_once, _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1);
return v___x_564_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules(void){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timestamp(lean_object* v_t_566_){
_start:
{
lean_object* v_time_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_575_; 
v_time_567_ = lean_ctor_get(v_t_566_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v_t_566_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_t_566_, 1);
lean_dec(v_unused_576_);
v___x_569_ = v_t_566_;
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_time_567_);
lean_dec(v_t_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 1, v___x_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_time_567_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(lean_object* v_transition_577_){
_start:
{
lean_object* v_localTimeType_578_; lean_object* v_gmtOffset_579_; uint8_t v_isDst_580_; lean_object* v_abbreviation_581_; lean_object* v_identifier_582_; lean_object* v___x_583_; 
v_localTimeType_578_ = lean_ctor_get(v_transition_577_, 1);
v_gmtOffset_579_ = lean_ctor_get(v_localTimeType_578_, 0);
v_isDst_580_ = lean_ctor_get_uint8(v_localTimeType_578_, sizeof(void*)*3);
v_abbreviation_581_ = lean_ctor_get(v_localTimeType_578_, 1);
v_identifier_582_ = lean_ctor_get(v_localTimeType_578_, 2);
lean_inc_ref(v_abbreviation_581_);
lean_inc_ref(v_identifier_582_);
lean_inc(v_gmtOffset_579_);
v___x_583_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_583_, 0, v_gmtOffset_579_);
lean_ctor_set(v___x_583_, 1, v_identifier_582_);
lean_ctor_set(v___x_583_, 2, v_abbreviation_581_);
lean_ctor_set_uint8(v___x_583_, sizeof(void*)*3, v_isDst_580_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition___boxed(lean_object* v_transition_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_transition_584_);
lean_dec_ref(v_transition_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(lean_object* v_value_586_, lean_object* v_as_587_, lean_object* v_j_588_){
_start:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_array_get_size(v_as_587_);
v___x_590_ = lean_nat_dec_lt(v_j_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec(v_j_588_);
v___x_591_ = lean_box(0);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v_time_593_; uint8_t v___x_594_; 
v___x_592_ = lean_array_fget_borrowed(v_as_587_, v_j_588_);
v_time_593_ = lean_ctor_get(v___x_592_, 0);
v___x_594_ = lean_int_dec_lt(v_value_586_, v_time_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_j_588_, v___x_595_);
lean_dec(v_j_588_);
v_j_588_ = v___x_596_;
goto _start;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_j_588_);
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0___boxed(lean_object* v_value_599_, lean_object* v_as_600_, lean_object* v_j_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_value_599_, v_as_600_, v_j_601_);
lean_dec_ref(v_as_600_);
lean_dec(v_value_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(lean_object* v_transitions_603_, lean_object* v_timestamp_604_){
_start:
{
lean_object* v_second_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_second_605_ = lean_ctor_get(v_timestamp_604_, 0);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_second_605_, v_transitions_603_, v___x_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_608_ = lean_array_get_size(v_transitions_603_);
v___x_609_ = lean_nat_dec_eq(v___x_608_, v___x_606_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_sub(v___x_608_, v___x_610_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
else
{
return v___x_607_;
}
}
else
{
lean_object* v_val_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_624_; 
v_val_613_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_624_ == 0)
{
v___x_615_ = v___x_607_;
v_isShared_616_ = v_isSharedCheck_624_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_val_613_);
lean_dec(v___x_607_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_624_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; 
v___x_617_ = lean_nat_dec_eq(v_val_613_, v___x_606_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_sub(v_val_613_, v___x_618_);
lean_dec(v_val_613_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_619_);
v___x_621_ = v___x_615_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_623_; 
lean_del_object(v___x_615_);
lean_dec(v_val_613_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp___boxed(lean_object* v_transitions_625_, lean_object* v_timestamp_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_625_, v_timestamp_626_);
lean_dec_ref(v_timestamp_626_);
lean_dec_ref(v_transitions_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object* v_transitions_628_, lean_object* v_timestamp_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_628_, v_timestamp_629_);
if (lean_obj_tag(v___x_630_) == 1)
{
lean_object* v_val_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_642_; 
v_val_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_642_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_642_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_val_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_642_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_array_get_size(v_transitions_628_);
v___x_636_ = lean_nat_dec_lt(v_val_631_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_del_object(v___x_633_);
lean_dec(v_val_631_);
v___x_637_ = lean_box(0);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_array_fget_borrowed(v_transitions_628_, v_val_631_);
lean_dec(v_val_631_);
lean_inc(v___x_638_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_638_);
v___x_640_ = v___x_633_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v___x_630_);
v___x_643_ = lean_box(0);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp___boxed(lean_object* v_transitions_644_, lean_object* v_timestamp_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_644_, v_timestamp_645_);
lean_dec_ref(v_timestamp_645_);
lean_dec_ref(v_transitions_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object* v_transitions_650_, lean_object* v_tm_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_650_, v_tm_651_);
if (lean_obj_tag(v___x_652_) == 1)
{
lean_object* v_val_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_val_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_val_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_657_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_val_653_);
lean_dec(v_val_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
else
{
lean_object* v___x_662_; 
lean_dec(v___x_652_);
v___x_662_ = ((lean_object*)(l_Std_Time_TimeZone_Transition_timezoneAt___closed__1));
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt___boxed(lean_object* v_transitions_663_, lean_object* v_tm_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_663_, v_tm_664_);
lean_dec_ref(v_tm_664_);
lean_dec_ref(v_transitions_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds_spec__0(lean_object* v_a_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Rat_ofInt(v_a_666_);
return v___x_667_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(86400u);
v___x_669_ = lean_nat_to_int(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(lean_object* v_rule_670_, lean_object* v_year_671_, lean_object* v_wallOffset_672_){
_start:
{
lean_object* v_spec_673_; lean_object* v_time_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v_spec_673_ = lean_ctor_get(v_rule_670_, 0);
lean_inc_ref(v_spec_673_);
v_time_674_ = lean_ctor_get(v_rule_670_, 1);
lean_inc(v_time_674_);
lean_dec_ref(v_rule_670_);
v___x_675_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDay(v_spec_673_, v_year_671_);
v___x_676_ = lean_obj_once(&l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0, &l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once, _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0);
v___x_677_ = lean_int_mul(v___x_675_, v___x_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_int_add(v___x_677_, v_time_674_);
lean_dec(v_time_674_);
lean_dec(v___x_677_);
v___x_679_ = lean_int_sub(v___x_678_, v_wallOffset_672_);
lean_dec(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___boxed(lean_object* v_rule_680_, lean_object* v_year_681_, lean_object* v_wallOffset_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_rule_680_, v_year_681_, v_wallOffset_682_);
lean_dec(v_wallOffset_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt(lean_object* v_rule_684_, lean_object* v_tm_685_){
_start:
{
lean_object* v_stdName_686_; lean_object* v_stdOffset_687_; lean_object* v_dst_688_; uint8_t v___x_689_; lean_object* v_stdTz_690_; 
v_stdName_686_ = lean_ctor_get(v_rule_684_, 0);
lean_inc_ref_n(v_stdName_686_, 2);
v_stdOffset_687_ = lean_ctor_get(v_rule_684_, 1);
lean_inc_n(v_stdOffset_687_, 2);
v_dst_688_ = lean_ctor_get(v_rule_684_, 2);
lean_inc(v_dst_688_);
lean_dec_ref(v_rule_684_);
v___x_689_ = 0;
v_stdTz_690_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_stdTz_690_, 0, v_stdOffset_687_);
lean_ctor_set(v_stdTz_690_, 1, v_stdName_686_);
lean_ctor_set(v_stdTz_690_, 2, v_stdName_686_);
lean_ctor_set_uint8(v_stdTz_690_, sizeof(void*)*3, v___x_689_);
if (lean_obj_tag(v_dst_688_) == 1)
{
lean_object* v_val_691_; lean_object* v_name_692_; lean_object* v_offset_693_; lean_object* v_start_694_; lean_object* v_end___695_; uint8_t v___x_696_; lean_object* v_dstTz_697_; 
v_val_691_ = lean_ctor_get(v_dst_688_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v_dst_688_, 1);
v_name_692_ = lean_ctor_get(v_val_691_, 0);
lean_inc_ref_n(v_name_692_, 2);
v_offset_693_ = lean_ctor_get(v_val_691_, 1);
lean_inc_n(v_offset_693_, 2);
v_start_694_ = lean_ctor_get(v_val_691_, 2);
lean_inc(v_start_694_);
v_end___695_ = lean_ctor_get(v_val_691_, 3);
lean_inc(v_end___695_);
lean_dec(v_val_691_);
v___x_696_ = 1;
v_dstTz_697_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_dstTz_697_, 0, v_offset_693_);
lean_ctor_set(v_dstTz_697_, 1, v_name_692_);
lean_ctor_set(v_dstTz_697_, 2, v_name_692_);
lean_ctor_set_uint8(v_dstTz_697_, sizeof(void*)*3, v___x_696_);
if (lean_obj_tag(v_start_694_) == 1)
{
if (lean_obj_tag(v_end___695_) == 1)
{
lean_object* v_val_698_; lean_object* v_val_699_; lean_object* v_second_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_year_704_; lean_object* v_dstStart_705_; lean_object* v_dstEnd_706_; uint8_t v___x_707_; 
v_val_698_ = lean_ctor_get(v_start_694_, 0);
lean_inc(v_val_698_);
lean_dec_ref_known(v_start_694_, 1);
v_val_699_ = lean_ctor_get(v_end___695_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v_end___695_, 1);
v_second_700_ = lean_ctor_get(v_tm_685_, 0);
v___x_701_ = lean_obj_once(&l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0, &l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once, _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0);
v___x_702_ = lean_int_ediv(v_second_700_, v___x_701_);
v___x_703_ = l_Std_Time_PlainDate_ofEpochDay(v___x_702_);
lean_dec(v___x_702_);
v_year_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc_n(v_year_704_, 2);
lean_dec_ref(v___x_703_);
v_dstStart_705_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_val_698_, v_year_704_, v_stdOffset_687_);
lean_dec(v_stdOffset_687_);
v_dstEnd_706_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_val_699_, v_year_704_, v_offset_693_);
lean_dec(v_offset_693_);
v___x_707_ = lean_int_dec_le(v_dstStart_705_, v_dstEnd_706_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; 
v___x_708_ = lean_int_dec_lt(v_second_700_, v_dstEnd_706_);
lean_dec(v_dstEnd_706_);
if (v___x_708_ == 0)
{
uint8_t v___x_709_; 
v___x_709_ = lean_int_dec_le(v_dstStart_705_, v_second_700_);
lean_dec(v_dstStart_705_);
if (v___x_709_ == 0)
{
lean_dec_ref_known(v_dstTz_697_, 3);
return v_stdTz_690_;
}
else
{
lean_dec_ref_known(v_stdTz_690_, 3);
return v_dstTz_697_;
}
}
else
{
lean_dec(v_dstStart_705_);
lean_dec_ref_known(v_stdTz_690_, 3);
return v_dstTz_697_;
}
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_int_dec_le(v_dstStart_705_, v_second_700_);
lean_dec(v_dstStart_705_);
if (v___x_710_ == 0)
{
lean_dec(v_dstEnd_706_);
lean_dec_ref_known(v_dstTz_697_, 3);
return v_stdTz_690_;
}
else
{
uint8_t v___x_711_; 
v___x_711_ = lean_int_dec_lt(v_second_700_, v_dstEnd_706_);
lean_dec(v_dstEnd_706_);
if (v___x_711_ == 0)
{
lean_dec_ref_known(v_dstTz_697_, 3);
return v_stdTz_690_;
}
else
{
lean_dec_ref_known(v_stdTz_690_, 3);
return v_dstTz_697_;
}
}
}
}
else
{
lean_dec_ref_known(v_start_694_, 1);
lean_dec_ref_known(v_dstTz_697_, 3);
lean_dec(v_end___695_);
lean_dec(v_offset_693_);
lean_dec(v_stdOffset_687_);
return v_stdTz_690_;
}
}
else
{
lean_dec_ref_known(v_dstTz_697_, 3);
lean_dec(v_end___695_);
lean_dec(v_start_694_);
lean_dec(v_offset_693_);
lean_dec(v_stdOffset_687_);
return v_stdTz_690_;
}
}
else
{
lean_dec(v_dst_688_);
lean_dec(v_stdOffset_687_);
return v_stdTz_690_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt___boxed(lean_object* v_rule_712_, lean_object* v_tm_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_rule_712_, v_tm_713_);
lean_dec_ref(v_tm_713_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(lean_object* v_second_715_, lean_object* v_00___716_){
_start:
{
uint8_t v___x_717_; lean_object* v___x_718_; 
v___x_717_ = 1;
v___x_718_ = l_Std_Time_TimeZone_Offset_toIsoString(v_second_715_, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object* v_second_721_, lean_object* v_identifier_722_, lean_object* v_abbreviation_723_){
_start:
{
uint8_t v___x_724_; uint8_t v___y_726_; lean_object* v___y_727_; uint8_t v___y_728_; lean_object* v___y_729_; lean_object* v___y_735_; 
v___x_724_ = 0;
if (lean_obj_tag(v_abbreviation_723_) == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_box(0);
lean_inc(v_second_721_);
v___x_742_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(v_second_721_, v___x_741_);
v___y_735_ = v___x_742_;
goto v___jp_734_;
}
else
{
lean_object* v_val_743_; 
v_val_743_ = lean_ctor_get(v_abbreviation_723_, 0);
lean_inc(v_val_743_);
lean_dec_ref_known(v_abbreviation_723_, 1);
v___y_735_ = v_val_743_;
goto v___jp_734_;
}
v___jp_725_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_730_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_730_, 0, v_second_721_);
lean_ctor_set(v___x_730_, 1, v___y_727_);
lean_ctor_set(v___x_730_, 2, v___y_729_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*3, v___x_724_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*3 + 1, v___y_728_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*3 + 2, v___y_726_);
v___x_731_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0));
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_733_, 0, v___x_730_);
lean_ctor_set(v___x_733_, 1, v___x_731_);
lean_ctor_set(v___x_733_, 2, v___x_732_);
return v___x_733_;
}
v___jp_734_:
{
uint8_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = 1;
v___x_737_ = 0;
if (lean_obj_tag(v_identifier_722_) == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_box(0);
lean_inc(v_second_721_);
v___x_739_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(v_second_721_, v___x_738_);
v___y_726_ = v___x_737_;
v___y_727_ = v___y_735_;
v___y_728_ = v___x_736_;
v___y_729_ = v___x_739_;
goto v___jp_725_;
}
else
{
lean_object* v_val_740_; 
v_val_740_ = lean_ctor_get(v_identifier_722_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v_identifier_722_, 1);
v___y_726_ = v___x_737_;
v___y_727_ = v___y_735_;
v___y_728_ = v___x_736_;
v___y_729_ = v_val_740_;
goto v___jp_725_;
}
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_nat_to_int(v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_UTC___closed__2));
v___x_750_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_UTC___closed__0, &l_Std_Time_TimeZone_ZoneRules_UTC___closed__0_once, _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0);
v___x_751_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_750_, v___x_749_, v___x_749_);
return v___x_751_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_UTC___closed__3, &l_Std_Time_TimeZone_ZoneRules_UTC___closed__3_once, _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(lean_object* v_zr_753_, lean_object* v_timestamp_754_){
_start:
{
lean_object* v_initialLocalTimeType_755_; lean_object* v_transitions_756_; lean_object* v_transitionRule_757_; lean_object* v___x_758_; 
v_initialLocalTimeType_755_ = lean_ctor_get(v_zr_753_, 0);
lean_inc_ref(v_initialLocalTimeType_755_);
v_transitions_756_ = lean_ctor_get(v_zr_753_, 1);
lean_inc_ref(v_transitions_756_);
v_transitionRule_757_ = lean_ctor_get(v_zr_753_, 2);
lean_inc(v_transitionRule_757_);
lean_dec_ref(v_zr_753_);
v___x_758_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_756_, v_timestamp_754_);
if (lean_obj_tag(v___x_758_) == 1)
{
lean_object* v_val_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = lean_array_get_size(v_transitions_756_);
v___x_761_ = lean_nat_dec_lt(v_val_759_, v___x_760_);
if (v___x_761_ == 0)
{
lean_dec(v_val_759_);
lean_dec(v_transitionRule_757_);
lean_dec_ref(v_transitions_756_);
return v_initialLocalTimeType_755_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
lean_dec_ref(v_initialLocalTimeType_755_);
v___x_762_ = lean_array_fget(v_transitions_756_, v_val_759_);
lean_dec_ref(v_transitions_756_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_val_759_, v___x_763_);
lean_dec(v_val_759_);
v___x_765_ = lean_nat_dec_eq(v___x_764_, v___x_760_);
lean_dec(v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v_localTimeType_766_; 
lean_dec(v_transitionRule_757_);
v_localTimeType_766_ = lean_ctor_get(v___x_762_, 1);
lean_inc_ref(v_localTimeType_766_);
lean_dec(v___x_762_);
return v_localTimeType_766_;
}
else
{
if (lean_obj_tag(v_transitionRule_757_) == 1)
{
lean_object* v_val_767_; lean_object* v_localTimeType_768_; lean_object* v_tz_769_; lean_object* v_offset_770_; lean_object* v_name_771_; lean_object* v_abbreviation_772_; uint8_t v_isDST_773_; uint8_t v_wall_774_; uint8_t v_utLocal_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_val_767_ = lean_ctor_get(v_transitionRule_757_, 0);
lean_inc(v_val_767_);
lean_dec_ref_known(v_transitionRule_757_, 1);
v_localTimeType_768_ = lean_ctor_get(v___x_762_, 1);
lean_inc_ref(v_localTimeType_768_);
lean_dec(v___x_762_);
v_tz_769_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_val_767_, v_timestamp_754_);
v_offset_770_ = lean_ctor_get(v_tz_769_, 0);
lean_inc(v_offset_770_);
v_name_771_ = lean_ctor_get(v_tz_769_, 1);
lean_inc_ref(v_name_771_);
v_abbreviation_772_ = lean_ctor_get(v_tz_769_, 2);
lean_inc_ref(v_abbreviation_772_);
v_isDST_773_ = lean_ctor_get_uint8(v_tz_769_, sizeof(void*)*3);
lean_dec_ref(v_tz_769_);
v_wall_774_ = lean_ctor_get_uint8(v_localTimeType_768_, sizeof(void*)*3 + 1);
v_utLocal_775_ = lean_ctor_get_uint8(v_localTimeType_768_, sizeof(void*)*3 + 2);
v_isSharedCheck_782_ = !lean_is_exclusive(v_localTimeType_768_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_783_ = lean_ctor_get(v_localTimeType_768_, 2);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_localTimeType_768_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_localTimeType_768_, 0);
lean_dec(v_unused_785_);
v___x_777_ = v_localTimeType_768_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_dec(v_localTimeType_768_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 2, v_name_771_);
lean_ctor_set(v___x_777_, 1, v_abbreviation_772_);
lean_ctor_set(v___x_777_, 0, v_offset_770_);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_offset_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_abbreviation_772_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_name_771_);
lean_ctor_set_uint8(v_reuseFailAlloc_781_, sizeof(void*)*3 + 1, v_wall_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_781_, sizeof(void*)*3 + 2, v_utLocal_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*3, v_isDST_773_);
return v___x_780_;
}
}
}
else
{
lean_object* v_localTimeType_786_; 
lean_dec(v_transitionRule_757_);
v_localTimeType_786_ = lean_ctor_get(v___x_762_, 1);
lean_inc_ref(v_localTimeType_786_);
lean_dec(v___x_762_);
return v_localTimeType_786_;
}
}
}
}
else
{
lean_dec(v___x_758_);
lean_dec(v_transitionRule_757_);
lean_dec_ref(v_transitions_756_);
return v_initialLocalTimeType_755_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp___boxed(lean_object* v_zr_787_, lean_object* v_timestamp_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_787_, v_timestamp_788_);
lean_dec_ref(v_timestamp_788_);
return v_res_789_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = lean_unsigned_to_nat(1000000000u);
v___x_791_ = lean_nat_to_int(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(lean_object* v_wallTime_792_, lean_object* v_as_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_b_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_797_ == 0)
{
return v_b_796_;
}
else
{
lean_object* v_snd_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_828_; 
v_snd_798_ = lean_ctor_get(v_b_796_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_b_796_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_b_796_, 0);
lean_dec(v_unused_829_);
v___x_800_ = v_b_796_;
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_snd_798_);
lean_dec(v_b_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_828_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_gmtOffset_802_; lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v_second_805_; lean_object* v_nano_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_gmtOffset_802_ = lean_ctor_get(v_snd_798_, 0);
v_a_803_ = lean_array_uget_borrowed(v_as_793_, v_i_795_);
lean_inc(v_a_803_);
v___x_804_ = l_Std_Time_TimeZone_Transition_timestamp(v_a_803_);
v_second_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_second_805_);
v_nano_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_nano_806_);
lean_dec_ref(v___x_804_);
v___x_807_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_808_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0);
v___x_809_ = lean_int_mul(v_second_805_, v___x_808_);
lean_dec(v_second_805_);
v___x_810_ = lean_int_add(v___x_809_, v_nano_806_);
lean_dec(v_nano_806_);
lean_dec(v___x_809_);
v___x_811_ = lean_int_mul(v_gmtOffset_802_, v___x_808_);
v___x_812_ = lean_int_add(v___x_811_, v___x_807_);
lean_dec(v___x_811_);
v___x_813_ = lean_int_add(v___x_810_, v___x_812_);
lean_dec(v___x_812_);
lean_dec(v___x_810_);
v___x_814_ = l_Std_Time_Duration_ofNanoseconds(v___x_813_);
lean_dec(v___x_813_);
v___x_815_ = l_Std_Time_Duration_instDecidableLt(v_wallTime_792_, v___x_814_);
lean_dec_ref(v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v_localTimeType_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
lean_dec(v_snd_798_);
v_localTimeType_816_ = lean_ctor_get(v_a_803_, 1);
v___x_817_ = lean_box(0);
lean_inc_ref(v_localTimeType_816_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_localTimeType_816_);
lean_ctor_set(v___x_800_, 0, v___x_817_);
v___x_819_ = v___x_800_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_localTimeType_816_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
size_t v___x_820_; size_t v___x_821_; 
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_i_795_, v___x_820_);
v_i_795_ = v___x_821_;
v_b_796_ = v___x_819_;
goto _start;
}
}
else
{
lean_object* v___x_824_; lean_object* v___x_826_; 
lean_inc(v_snd_798_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_snd_798_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_824_);
v___x_826_ = v___x_800_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_snd_798_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___boxed(lean_object* v_wallTime_830_, lean_object* v_as_831_, lean_object* v_sz_832_, lean_object* v_i_833_, lean_object* v_b_834_){
_start:
{
size_t v_sz_boxed_835_; size_t v_i_boxed_836_; lean_object* v_res_837_; 
v_sz_boxed_835_ = lean_unbox_usize(v_sz_832_);
lean_dec(v_sz_832_);
v_i_boxed_836_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_830_, v_as_831_, v_sz_boxed_835_, v_i_boxed_836_, v_b_834_);
lean_dec_ref(v_as_831_);
lean_dec_ref(v_wallTime_830_);
return v_res_837_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_839_ = lean_int_neg(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object* v_zr_840_, lean_object* v_wallTime_841_){
_start:
{
lean_object* v_initialLocalTimeType_842_; lean_object* v_transitions_843_; lean_object* v_transitionRule_844_; lean_object* v___x_845_; lean_object* v___x_846_; size_t v_sz_847_; size_t v___x_848_; lean_object* v___x_849_; lean_object* v_fst_850_; 
v_initialLocalTimeType_842_ = lean_ctor_get(v_zr_840_, 0);
lean_inc_ref(v_initialLocalTimeType_842_);
v_transitions_843_ = lean_ctor_get(v_zr_840_, 1);
lean_inc_ref(v_transitions_843_);
v_transitionRule_844_ = lean_ctor_get(v_zr_840_, 2);
lean_inc(v_transitionRule_844_);
lean_dec_ref(v_zr_840_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v_initialLocalTimeType_842_);
v_sz_847_ = lean_array_size(v_transitions_843_);
v___x_848_ = ((size_t)0ULL);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_841_, v_transitions_843_, v_sz_847_, v___x_848_, v___x_846_);
lean_dec_ref(v_transitions_843_);
v_fst_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_fst_850_);
if (lean_obj_tag(v_fst_850_) == 0)
{
if (lean_obj_tag(v_transitionRule_844_) == 1)
{
lean_object* v_snd_851_; lean_object* v_val_852_; lean_object* v_gmtOffset_853_; uint8_t v_wall_854_; uint8_t v_utLocal_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_878_; 
v_snd_851_ = lean_ctor_get(v___x_849_, 1);
lean_inc(v_snd_851_);
lean_dec_ref(v___x_849_);
v_val_852_ = lean_ctor_get(v_transitionRule_844_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v_transitionRule_844_, 1);
v_gmtOffset_853_ = lean_ctor_get(v_snd_851_, 0);
v_wall_854_ = lean_ctor_get_uint8(v_snd_851_, sizeof(void*)*3 + 1);
v_utLocal_855_ = lean_ctor_get_uint8(v_snd_851_, sizeof(void*)*3 + 2);
v_isSharedCheck_878_ = !lean_is_exclusive(v_snd_851_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; lean_object* v_unused_880_; 
v_unused_879_ = lean_ctor_get(v_snd_851_, 2);
lean_dec(v_unused_879_);
v_unused_880_ = lean_ctor_get(v_snd_851_, 1);
lean_dec(v_unused_880_);
v___x_857_ = v_snd_851_;
v_isShared_858_ = v_isSharedCheck_878_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_gmtOffset_853_);
lean_dec(v_snd_851_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_878_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_second_859_; lean_object* v_nano_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_offset_871_; lean_object* v_name_872_; lean_object* v_abbreviation_873_; uint8_t v_isDST_874_; lean_object* v___x_876_; 
v_second_859_ = lean_ctor_get(v_wallTime_841_, 0);
v_nano_860_ = lean_ctor_get(v_wallTime_841_, 1);
v___x_861_ = lean_int_neg(v_gmtOffset_853_);
lean_dec(v_gmtOffset_853_);
v___x_862_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0, &l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0_once, _init_l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0);
v___x_863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0);
v___x_864_ = lean_int_mul(v_second_859_, v___x_863_);
v___x_865_ = lean_int_add(v___x_864_, v_nano_860_);
lean_dec(v___x_864_);
v___x_866_ = lean_int_mul(v___x_861_, v___x_863_);
lean_dec(v___x_861_);
v___x_867_ = lean_int_add(v___x_866_, v___x_862_);
lean_dec(v___x_866_);
v___x_868_ = lean_int_add(v___x_865_, v___x_867_);
lean_dec(v___x_867_);
lean_dec(v___x_865_);
v___x_869_ = l_Std_Time_Duration_ofNanoseconds(v___x_868_);
lean_dec(v___x_868_);
v___x_870_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_val_852_, v___x_869_);
lean_dec_ref(v___x_869_);
v_offset_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_offset_871_);
v_name_872_ = lean_ctor_get(v___x_870_, 1);
lean_inc_ref(v_name_872_);
v_abbreviation_873_ = lean_ctor_get(v___x_870_, 2);
lean_inc_ref(v_abbreviation_873_);
v_isDST_874_ = lean_ctor_get_uint8(v___x_870_, sizeof(void*)*3);
lean_dec_ref(v___x_870_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 2, v_name_872_);
lean_ctor_set(v___x_857_, 1, v_abbreviation_873_);
lean_ctor_set(v___x_857_, 0, v_offset_871_);
v___x_876_ = v___x_857_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_offset_871_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_abbreviation_873_);
lean_ctor_set(v_reuseFailAlloc_877_, 2, v_name_872_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*3 + 1, v_wall_854_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*3 + 2, v_utLocal_855_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*3, v_isDST_874_);
return v___x_876_;
}
}
}
else
{
lean_object* v_snd_881_; 
lean_dec(v_transitionRule_844_);
v_snd_881_ = lean_ctor_get(v___x_849_, 1);
lean_inc(v_snd_881_);
lean_dec_ref(v___x_849_);
return v_snd_881_;
}
}
else
{
lean_object* v_val_882_; 
lean_dec_ref(v___x_849_);
lean_dec(v_transitionRule_844_);
v_val_882_ = lean_ctor_get(v_fst_850_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v_fst_850_, 1);
return v_val_882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___boxed(lean_object* v_zr_883_, lean_object* v_wallTime_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_883_, v_wallTime_884_);
lean_dec_ref(v_wallTime_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object* v_zr_886_, lean_object* v_tm_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_886_, v_tm_887_);
v___x_889_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_888_);
lean_dec_ref(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt___boxed(lean_object* v_zr_890_, lean_object* v_tm_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_zr_890_, v_tm_891_);
lean_dec_ref(v_tm_891_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone(lean_object* v_tz_893_){
_start:
{
lean_object* v_offset_894_; lean_object* v_name_895_; lean_object* v_abbreviation_896_; uint8_t v_isDST_897_; uint8_t v___x_898_; uint8_t v___x_899_; lean_object* v_ltt_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_offset_894_ = lean_ctor_get(v_tz_893_, 0);
v_name_895_ = lean_ctor_get(v_tz_893_, 1);
v_abbreviation_896_ = lean_ctor_get(v_tz_893_, 2);
v_isDST_897_ = lean_ctor_get_uint8(v_tz_893_, sizeof(void*)*3);
v___x_898_ = 0;
v___x_899_ = 1;
lean_inc_ref(v_name_895_);
lean_inc_ref(v_abbreviation_896_);
lean_inc(v_offset_894_);
v_ltt_900_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_900_, 0, v_offset_894_);
lean_ctor_set(v_ltt_900_, 1, v_abbreviation_896_);
lean_ctor_set(v_ltt_900_, 2, v_name_895_);
lean_ctor_set_uint8(v_ltt_900_, sizeof(void*)*3, v_isDST_897_);
lean_ctor_set_uint8(v_ltt_900_, sizeof(void*)*3 + 1, v___x_898_);
lean_ctor_set_uint8(v_ltt_900_, sizeof(void*)*3 + 2, v___x_899_);
v___x_901_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0));
v___x_902_ = lean_box(0);
v___x_903_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_903_, 0, v_ltt_900_);
lean_ctor_set(v___x_903_, 1, v___x_901_);
lean_ctor_set(v___x_903_, 2, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone___boxed(lean_object* v_tz_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_Time_TimeZone_ZoneRules_ofTimeZone(v_tz_904_);
lean_dec_ref(v_tz_904_);
return v_res_905_;
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
