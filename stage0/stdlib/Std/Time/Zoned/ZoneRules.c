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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_toCtorIdx(uint8_t v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Time_TimeZone_UTLocal_ctorIdx(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_toCtorIdx___boxed(lean_object* v_x_9_){
_start:
{
uint8_t v_x_4__boxed_10_; lean_object* v_res_11_; 
v_x_4__boxed_10_ = lean_unbox(v_x_9_);
v_res_11_ = l_Std_Time_TimeZone_UTLocal_toCtorIdx(v_x_4__boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(lean_object* v_k_12_){
_start:
{
lean_inc(v_k_12_);
return v_k_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___redArg___boxed(lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(v_k_13_);
lean_dec(v_k_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, uint8_t v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_inc(v_k_19_);
return v_k_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
uint8_t v_t_boxed_25_; lean_object* v_res_26_; 
v_t_boxed_25_ = lean_unbox(v_t_22_);
v_res_26_ = l_Std_Time_TimeZone_UTLocal_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_boxed_25_, v_h_23_, v_k_24_);
lean_dec(v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(lean_object* v_ut_27_){
_start:
{
lean_inc(v_ut_27_);
return v_ut_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___redArg___boxed(lean_object* v_ut_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(v_ut_28_);
lean_dec(v_ut_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim(lean_object* v_motive_30_, uint8_t v_t_31_, lean_object* v_h_32_, lean_object* v_ut_33_){
_start:
{
lean_inc(v_ut_33_);
return v_ut_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___boxed(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_ut_37_){
_start:
{
uint8_t v_t_boxed_38_; lean_object* v_res_39_; 
v_t_boxed_38_ = lean_unbox(v_t_35_);
v_res_39_ = l_Std_Time_TimeZone_UTLocal_ut_elim(v_motive_34_, v_t_boxed_38_, v_h_36_, v_ut_37_);
lean_dec(v_ut_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___redArg(lean_object* v_local_40_){
_start:
{
lean_inc(v_local_40_);
return v_local_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___redArg___boxed(lean_object* v_local_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_Time_TimeZone_UTLocal_local_elim___redArg(v_local_41_);
lean_dec(v_local_41_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim(lean_object* v_motive_43_, uint8_t v_t_44_, lean_object* v_h_45_, lean_object* v_local_46_){
_start:
{
lean_inc(v_local_46_);
return v_local_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___boxed(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_local_50_){
_start:
{
uint8_t v_t_boxed_51_; lean_object* v_res_52_; 
v_t_boxed_51_ = lean_unbox(v_t_48_);
v_res_52_ = l_Std_Time_TimeZone_UTLocal_local_elim(v_motive_47_, v_t_boxed_51_, v_h_49_, v_local_50_);
lean_dec(v_local_50_);
return v_res_52_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(2u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr(uint8_t v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___y_66_; lean_object* v___y_73_; 
if (v_x_63_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1024u);
v___x_80_ = lean_nat_dec_le(v___x_79_, v_prec_64_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_66_ = v___x_81_;
goto v___jp_65_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_66_ = v___x_82_;
goto v___jp_65_;
}
}
else
{
lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(1024u);
v___x_84_ = lean_nat_dec_le(v___x_83_, v_prec_64_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_73_ = v___x_85_;
goto v___jp_72_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_73_ = v___x_86_;
goto v___jp_72_;
}
}
v___jp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_67_ = ((lean_object*)(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1));
lean_inc(v___y_66_);
v___x_68_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_68_, 0, v___y_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = 0;
v___x_70_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_70_, 0, v___x_68_);
lean_ctor_set_uint8(v___x_70_, sizeof(void*)*1, v___x_69_);
v___x_71_ = l_Repr_addAppParen(v___x_70_, v_prec_64_);
return v___x_71_;
}
v___jp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = ((lean_object*)(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3));
lean_inc(v___y_73_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___y_73_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = 0;
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_76_);
v___x_78_ = l_Repr_addAppParen(v___x_77_, v_prec_64_);
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_121__boxed_89_; lean_object* v_res_90_; 
v_x_121__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_x_121__boxed_89_, v_prec_88_);
lean_dec(v_prec_88_);
return v_res_90_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_instInhabitedUTLocal_default(void){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_instInhabitedUTLocal(void){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx(uint8_t v_x_95_){
_start:
{
if (v_x_95_ == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_unsigned_to_nat(0u);
return v___x_96_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = lean_unsigned_to_nat(1u);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx___boxed(lean_object* v_x_98_){
_start:
{
uint8_t v_x_boxed_99_; lean_object* v_res_100_; 
v_x_boxed_99_ = lean_unbox(v_x_98_);
v_res_100_ = l_Std_Time_TimeZone_StdWall_ctorIdx(v_x_boxed_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_toCtorIdx(uint8_t v_x_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Std_Time_TimeZone_StdWall_ctorIdx(v_x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_toCtorIdx___boxed(lean_object* v_x_103_){
_start:
{
uint8_t v_x_4__boxed_104_; lean_object* v_res_105_; 
v_x_4__boxed_104_ = lean_unbox(v_x_103_);
v_res_105_ = l_Std_Time_TimeZone_StdWall_toCtorIdx(v_x_4__boxed_104_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___redArg(lean_object* v_k_106_){
_start:
{
lean_inc(v_k_106_);
return v_k_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___redArg___boxed(lean_object* v_k_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_Time_TimeZone_StdWall_ctorElim___redArg(v_k_107_);
lean_dec(v_k_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim(lean_object* v_motive_109_, lean_object* v_ctorIdx_110_, uint8_t v_t_111_, lean_object* v_h_112_, lean_object* v_k_113_){
_start:
{
lean_inc(v_k_113_);
return v_k_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___boxed(lean_object* v_motive_114_, lean_object* v_ctorIdx_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_k_118_){
_start:
{
uint8_t v_t_boxed_119_; lean_object* v_res_120_; 
v_t_boxed_119_ = lean_unbox(v_t_116_);
v_res_120_ = l_Std_Time_TimeZone_StdWall_ctorElim(v_motive_114_, v_ctorIdx_115_, v_t_boxed_119_, v_h_117_, v_k_118_);
lean_dec(v_k_118_);
lean_dec(v_ctorIdx_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___redArg(lean_object* v_wall_121_){
_start:
{
lean_inc(v_wall_121_);
return v_wall_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___redArg___boxed(lean_object* v_wall_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Time_TimeZone_StdWall_wall_elim___redArg(v_wall_122_);
lean_dec(v_wall_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim(lean_object* v_motive_124_, uint8_t v_t_125_, lean_object* v_h_126_, lean_object* v_wall_127_){
_start:
{
lean_inc(v_wall_127_);
return v_wall_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___boxed(lean_object* v_motive_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_wall_131_){
_start:
{
uint8_t v_t_boxed_132_; lean_object* v_res_133_; 
v_t_boxed_132_ = lean_unbox(v_t_129_);
v_res_133_ = l_Std_Time_TimeZone_StdWall_wall_elim(v_motive_128_, v_t_boxed_132_, v_h_130_, v_wall_131_);
lean_dec(v_wall_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___redArg(lean_object* v_standard_134_){
_start:
{
lean_inc(v_standard_134_);
return v_standard_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___redArg___boxed(lean_object* v_standard_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_Time_TimeZone_StdWall_standard_elim___redArg(v_standard_135_);
lean_dec(v_standard_135_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim(lean_object* v_motive_137_, uint8_t v_t_138_, lean_object* v_h_139_, lean_object* v_standard_140_){
_start:
{
lean_inc(v_standard_140_);
return v_standard_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___boxed(lean_object* v_motive_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_standard_144_){
_start:
{
uint8_t v_t_boxed_145_; lean_object* v_res_146_; 
v_t_boxed_145_ = lean_unbox(v_t_142_);
v_res_146_ = l_Std_Time_TimeZone_StdWall_standard_elim(v_motive_141_, v_t_boxed_145_, v_h_143_, v_standard_144_);
lean_dec(v_standard_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprStdWall_repr(uint8_t v_x_153_, lean_object* v_prec_154_){
_start:
{
lean_object* v___y_156_; lean_object* v___y_163_; 
if (v_x_153_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(1024u);
v___x_170_ = lean_nat_dec_le(v___x_169_, v_prec_154_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_156_ = v___x_171_;
goto v___jp_155_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_156_ = v___x_172_;
goto v___jp_155_;
}
}
else
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(1024u);
v___x_174_ = lean_nat_dec_le(v___x_173_, v_prec_154_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_163_ = v___x_175_;
goto v___jp_162_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_163_ = v___x_176_;
goto v___jp_162_;
}
}
v___jp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = ((lean_object*)(l_Std_Time_TimeZone_instReprStdWall_repr___closed__1));
lean_inc(v___y_156_);
v___x_158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_158_, 0, v___y_156_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = 0;
v___x_160_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_160_, 0, v___x_158_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1, v___x_159_);
v___x_161_ = l_Repr_addAppParen(v___x_160_, v_prec_154_);
return v___x_161_;
}
v___jp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_164_ = ((lean_object*)(l_Std_Time_TimeZone_instReprStdWall_repr___closed__3));
lean_inc(v___y_163_);
v___x_165_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_165_, 0, v___y_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_166_);
v___x_168_ = l_Repr_addAppParen(v___x_167_, v_prec_154_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprStdWall_repr___boxed(lean_object* v_x_177_, lean_object* v_prec_178_){
_start:
{
uint8_t v_x_117__boxed_179_; lean_object* v_res_180_; 
v_x_117__boxed_179_ = lean_unbox(v_x_177_);
v_res_180_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_x_117__boxed_179_, v_prec_178_);
lean_dec(v_prec_178_);
return v_res_180_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_instInhabitedStdWall_default(void){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = 0;
return v___x_183_;
}
}
static uint8_t _init_l_Std_Time_TimeZone_instInhabitedStdWall(void){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = 0;
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instReprLocalTimeType_repr_spec__0(lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = lean_nat_to_int(v_a_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(13u);
v___x_201_ = lean_nat_to_int(v___x_200_);
return v___x_201_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(9u);
v___x_209_ = lean_nat_to_int(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(16u);
v___x_214_ = lean_nat_to_int(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_unsigned_to_nat(8u);
v___x_219_ = lean_nat_to_int(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(11u);
v___x_224_ = lean_nat_to_int(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_unsigned_to_nat(14u);
v___x_229_ = lean_nat_to_int(v___x_228_);
return v___x_229_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__0));
v___x_232_ = lean_string_length(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__26);
v___x_234_ = lean_nat_to_int(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(lean_object* v_x_239_){
_start:
{
lean_object* v_gmtOffset_240_; uint8_t v_isDst_241_; lean_object* v_abbreviation_242_; uint8_t v_wall_243_; uint8_t v_utLocal_244_; lean_object* v_identifier_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_gmtOffset_240_ = lean_ctor_get(v_x_239_, 0);
lean_inc(v_gmtOffset_240_);
v_isDst_241_ = lean_ctor_get_uint8(v_x_239_, sizeof(void*)*3);
v_abbreviation_242_ = lean_ctor_get(v_x_239_, 1);
lean_inc_ref(v_abbreviation_242_);
v_wall_243_ = lean_ctor_get_uint8(v_x_239_, sizeof(void*)*3 + 1);
v_utLocal_244_ = lean_ctor_get_uint8(v_x_239_, sizeof(void*)*3 + 2);
v_identifier_245_ = lean_ctor_get(v_x_239_, 2);
lean_inc_ref(v_identifier_245_);
lean_dec_ref(v_x_239_);
v___x_246_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5));
v___x_247_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__6));
v___x_248_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__7);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_gmtOffset_240_);
lean_dec(v_gmtOffset_240_);
v___x_251_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_248_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = 0;
v___x_253_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set_uint8(v___x_253_, sizeof(void*)*1, v___x_252_);
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_247_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9));
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_box(1);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__11));
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_246_);
v___x_262_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__12);
v___x_263_ = l_Bool_repr___redArg(v_isDst_241_);
v___x_264_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_252_);
v___x_266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_261_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_255_);
v___x_268_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_257_);
v___x_269_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__14));
v___x_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_246_);
v___x_272_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__15);
v___x_273_ = l_String_quote(v_abbreviation_242_);
v___x_274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_272_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_252_);
v___x_277_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_271_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_255_);
v___x_279_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_257_);
v___x_280_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__17));
v___x_281_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_246_);
v___x_283_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18);
v___x_284_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_wall_243_, v___x_249_);
v___x_285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*1, v___x_252_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_282_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_255_);
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_257_);
v___x_290_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__20));
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_246_);
v___x_293_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__21);
v___x_294_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_utLocal_244_, v___x_249_);
v___x_295_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1, v___x_252_);
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_292_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_255_);
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_257_);
v___x_300_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__23));
v___x_301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_246_);
v___x_303_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__24);
v___x_304_ = l_String_quote(v_identifier_245_);
v___x_305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set_uint8(v___x_307_, sizeof(void*)*1, v___x_252_);
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_302_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27);
v___x_310_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28));
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_308_);
v___x_312_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29));
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_309_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*1, v___x_252_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr(lean_object* v_x_316_, lean_object* v_prec_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_x_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprLocalTimeType_repr___boxed(lean_object* v_x_319_, lean_object* v_prec_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr(v_x_319_, v_prec_320_);
lean_dec(v_prec_320_);
return v_res_321_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_nat_to_int(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2(void){
_start:
{
uint8_t v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_327_ = 0;
v___x_328_ = 0;
v___x_329_ = ((lean_object*)(l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__1));
v___x_330_ = 0;
v___x_331_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_332_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_329_);
lean_ctor_set(v___x_332_, 2, v___x_329_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*3, v___x_330_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*3 + 1, v___x_328_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*3 + 2, v___x_327_);
return v___x_332_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default(void){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__2);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instInhabitedLocalTimeType_default_spec__0(lean_object* v_a_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_nat_to_int(v_a_334_);
v___x_336_ = l_Rat_ofInt(v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType(void){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object* v_time_338_){
_start:
{
lean_object* v_gmtOffset_339_; uint8_t v_isDst_340_; lean_object* v_abbreviation_341_; lean_object* v_identifier_342_; lean_object* v___x_343_; 
v_gmtOffset_339_ = lean_ctor_get(v_time_338_, 0);
v_isDst_340_ = lean_ctor_get_uint8(v_time_338_, sizeof(void*)*3);
v_abbreviation_341_ = lean_ctor_get(v_time_338_, 1);
v_identifier_342_ = lean_ctor_get(v_time_338_, 2);
lean_inc_ref(v_abbreviation_341_);
lean_inc_ref(v_identifier_342_);
lean_inc(v_gmtOffset_339_);
v___x_343_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_343_, 0, v_gmtOffset_339_);
lean_ctor_set(v___x_343_, 1, v_identifier_342_);
lean_ctor_set(v___x_343_, 2, v_abbreviation_341_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*3, v_isDst_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone___boxed(lean_object* v_time_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_time_344_);
lean_dec_ref(v_time_344_);
return v_res_345_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(17u);
v___x_359_ = lean_nat_to_int(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr___redArg(lean_object* v_x_360_){
_start:
{
lean_object* v_time_361_; lean_object* v_localTimeType_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_396_; 
v_time_361_ = lean_ctor_get(v_x_360_, 0);
v_localTimeType_362_ = lean_ctor_get(v_x_360_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_x_360_);
if (v_isSharedCheck_396_ == 0)
{
v___x_364_ = v_x_360_;
v_isShared_365_ = v_isSharedCheck_396_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_localTimeType_362_);
lean_inc(v_time_361_);
lean_dec(v_x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_396_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_366_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5));
v___x_367_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__3));
v___x_368_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__18);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = l_Std_Time_Second_instReprOffset___lam__0(v_time_361_, v___x_369_);
lean_dec(v_time_361_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 4);
lean_ctor_set(v___x_364_, 1, v___x_370_);
lean_ctor_set(v___x_364_, 0, v___x_368_);
v___x_372_ = v___x_364_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_395_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_373_ = 0;
v___x_374_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set_uint8(v___x_374_, sizeof(void*)*1, v___x_373_);
v___x_375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_367_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9));
v___x_377_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_box(1);
v___x_379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
v___x_380_ = ((lean_object*)(l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__5));
v___x_381_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_379_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_366_);
v___x_383_ = lean_obj_once(&l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6, &l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6_once, _init_l_Std_Time_TimeZone_instReprTransition_repr___redArg___closed__6);
v___x_384_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_localTimeType_362_);
v___x_385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*1, v___x_373_);
v___x_387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_382_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27);
v___x_389_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28));
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_387_);
v___x_391_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29));
v___x_392_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_388_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*1, v___x_373_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr(lean_object* v_x_397_, lean_object* v_prec_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_x_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprTransition_repr___boxed(lean_object* v_x_400_, lean_object* v_prec_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_Time_TimeZone_instReprTransition_repr(v_x_400_, v_prec_401_);
lean_dec(v_prec_401_);
return v_res_402_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v___x_406_ = l_Std_Time_Second_instInhabitedOffset;
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition_default(void){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0, &l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0);
return v___x_408_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition(void){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_Time_TimeZone_instInhabitedTransition_default;
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(lean_object* v_x_416_, lean_object* v_x_417_){
_start:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v___x_418_; 
v___x_418_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__1));
return v___x_418_;
}
else
{
lean_object* v_val_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_val_419_ = lean_ctor_get(v_x_416_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_x_416_, 1);
v___x_420_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__3));
v___x_421_ = l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(v_val_419_);
v___x_422_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Repr_addAppParen(v___x_422_, v_x_417_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___boxed(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(v_x_424_, v_x_425_);
lean_dec(v_x_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_dec(v_x_427_);
return v_x_428_;
}
else
{
lean_object* v_head_430_; lean_object* v_tail_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_441_; 
v_head_430_ = lean_ctor_get(v_x_429_, 0);
v_tail_431_ = lean_ctor_get(v_x_429_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_429_);
if (v_isSharedCheck_441_ == 0)
{
v___x_433_ = v_x_429_;
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_tail_431_);
lean_inc(v_head_430_);
lean_dec(v_x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
lean_inc(v_x_427_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 5);
lean_ctor_set(v___x_433_, 1, v_x_427_);
lean_ctor_set(v___x_433_, 0, v_x_428_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_x_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_x_427_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_430_);
v___x_438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v_x_428_ = v___x_438_;
v_x_429_ = v_tail_431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_dec(v_x_442_);
return v_x_443_;
}
else
{
lean_object* v_head_445_; lean_object* v_tail_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_456_; 
v_head_445_ = lean_ctor_get(v_x_444_, 0);
v_tail_446_ = lean_ctor_get(v_x_444_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_456_ == 0)
{
v___x_448_ = v_x_444_;
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_tail_446_);
lean_inc(v_head_445_);
lean_dec(v_x_444_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
lean_inc(v_x_442_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 5);
lean_ctor_set(v___x_448_, 1, v_x_442_);
lean_ctor_set(v___x_448_, 0, v_x_443_);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_x_443_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_x_442_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_445_);
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(v_x_442_, v___x_453_, v_tail_446_);
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_459_; 
lean_dec(v_x_458_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v_tail_460_; 
v_tail_460_ = lean_ctor_get(v_x_457_, 1);
if (lean_obj_tag(v_tail_460_) == 0)
{
lean_object* v_head_461_; lean_object* v___x_462_; 
lean_dec(v_x_458_);
v_head_461_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_head_461_);
lean_dec_ref_known(v_x_457_, 2);
v___x_462_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_461_);
return v___x_462_;
}
else
{
lean_object* v_head_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_inc(v_tail_460_);
v_head_463_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_head_463_);
lean_dec_ref_known(v_x_457_, 2);
v___x_464_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_463_);
v___x_465_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(v_x_458_, v___x_464_, v_tail_460_);
return v___x_465_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0));
v___x_472_ = lean_string_length(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3);
v___x_474_ = lean_nat_to_int(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(lean_object* v_xs_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_483_ = lean_array_get_size(v_xs_482_);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = lean_nat_dec_eq(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_486_ = lean_array_to_list(v_xs_482_);
v___x_487_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1));
v___x_488_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(v___x_486_, v___x_487_);
v___x_489_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4);
v___x_490_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5));
v___x_491_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v___x_488_);
v___x_492_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6));
v___x_493_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_489_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = l_Std_Format_fill(v___x_494_);
return v___x_495_;
}
else
{
lean_object* v___x_496_; 
lean_dec_ref(v_xs_482_);
v___x_496_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8));
return v___x_496_;
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(24u);
v___x_507_ = lean_nat_to_int(v___x_506_);
return v___x_507_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(15u);
v___x_512_ = lean_nat_to_int(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(18u);
v___x_517_ = lean_nat_to_int(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(lean_object* v_x_518_){
_start:
{
lean_object* v_initialLocalTimeType_519_; lean_object* v_transitions_520_; lean_object* v_transitionRule_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_initialLocalTimeType_519_ = lean_ctor_get(v_x_518_, 0);
lean_inc_ref(v_initialLocalTimeType_519_);
v_transitions_520_ = lean_ctor_get(v_x_518_, 1);
lean_inc_ref(v_transitions_520_);
v_transitionRule_521_ = lean_ctor_get(v_x_518_, 2);
lean_inc(v_transitionRule_521_);
lean_dec_ref(v_x_518_);
v___x_522_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5));
v___x_523_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3));
v___x_524_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4);
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_initialLocalTimeType_519_);
v___x_527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = 0;
v___x_529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*1, v___x_528_);
v___x_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_523_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9));
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_box(1);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6));
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_522_);
v___x_538_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7);
v___x_539_ = l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(v_transitions_520_);
v___x_540_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*1, v___x_528_);
v___x_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_537_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___x_531_);
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_533_);
v___x_545_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__9));
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_522_);
v___x_548_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10);
v___x_549_ = l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(v_transitionRule_521_, v___x_525_);
v___x_550_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set_uint8(v___x_551_, sizeof(void*)*1, v___x_528_);
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_547_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27);
v___x_554_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28));
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v___x_552_);
v___x_556_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29));
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_553_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*1, v___x_528_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr(lean_object* v_x_560_, lean_object* v_prec_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(v_x_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___boxed(lean_object* v_x_563_, lean_object* v_prec_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_Time_TimeZone_instReprZoneRules_repr(v_x_563_, v_prec_564_);
lean_dec(v_prec_564_);
return v_res_565_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_box(0);
v___x_571_ = ((lean_object*)(l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0));
v___x_572_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v___x_573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_571_);
lean_ctor_set(v___x_573_, 2, v___x_570_);
return v___x_573_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1, &l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1_once, _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1);
return v___x_574_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timestamp(lean_object* v_t_576_){
_start:
{
lean_object* v_time_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_585_; 
v_time_577_ = lean_ctor_get(v_t_576_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v_t_576_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; 
v_unused_586_ = lean_ctor_get(v_t_576_, 1);
lean_dec(v_unused_586_);
v___x_579_ = v_t_576_;
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_time_577_);
lean_dec(v_t_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_585_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v___x_581_);
v___x_583_ = v___x_579_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_time_577_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(lean_object* v_transition_587_){
_start:
{
lean_object* v_localTimeType_588_; lean_object* v_gmtOffset_589_; uint8_t v_isDst_590_; lean_object* v_abbreviation_591_; lean_object* v_identifier_592_; lean_object* v___x_593_; 
v_localTimeType_588_ = lean_ctor_get(v_transition_587_, 1);
v_gmtOffset_589_ = lean_ctor_get(v_localTimeType_588_, 0);
v_isDst_590_ = lean_ctor_get_uint8(v_localTimeType_588_, sizeof(void*)*3);
v_abbreviation_591_ = lean_ctor_get(v_localTimeType_588_, 1);
v_identifier_592_ = lean_ctor_get(v_localTimeType_588_, 2);
lean_inc_ref(v_abbreviation_591_);
lean_inc_ref(v_identifier_592_);
lean_inc(v_gmtOffset_589_);
v___x_593_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_593_, 0, v_gmtOffset_589_);
lean_ctor_set(v___x_593_, 1, v_identifier_592_);
lean_ctor_set(v___x_593_, 2, v_abbreviation_591_);
lean_ctor_set_uint8(v___x_593_, sizeof(void*)*3, v_isDst_590_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition___boxed(lean_object* v_transition_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_transition_594_);
lean_dec_ref(v_transition_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(lean_object* v_value_596_, lean_object* v_as_597_, lean_object* v_j_598_){
_start:
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = lean_array_get_size(v_as_597_);
v___x_600_ = lean_nat_dec_lt(v_j_598_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
lean_dec(v_j_598_);
v___x_601_ = lean_box(0);
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v_time_603_; uint8_t v___x_604_; 
v___x_602_ = lean_array_fget_borrowed(v_as_597_, v_j_598_);
v_time_603_ = lean_ctor_get(v___x_602_, 0);
v___x_604_ = lean_int_dec_lt(v_value_596_, v_time_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_nat_add(v_j_598_, v___x_605_);
lean_dec(v_j_598_);
v_j_598_ = v___x_606_;
goto _start;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v_j_598_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0___boxed(lean_object* v_value_609_, lean_object* v_as_610_, lean_object* v_j_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_value_609_, v_as_610_, v_j_611_);
lean_dec_ref(v_as_610_);
lean_dec(v_value_609_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(lean_object* v_transitions_613_, lean_object* v_timestamp_614_){
_start:
{
lean_object* v_second_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_second_615_ = lean_ctor_get(v_timestamp_614_, 0);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_second_615_, v_transitions_613_, v___x_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_array_get_size(v_transitions_613_);
v___x_619_ = lean_nat_dec_eq(v___x_618_, v___x_616_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_sub(v___x_618_, v___x_620_);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
else
{
return v___x_617_;
}
}
else
{
lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_634_; 
v_val_623_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_634_ == 0)
{
v___x_625_ = v___x_617_;
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v___x_617_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_eq(v_val_623_, v___x_616_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_sub(v_val_623_, v___x_628_);
lean_dec(v_val_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_629_);
v___x_631_ = v___x_625_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v___x_633_; 
lean_del_object(v___x_625_);
lean_dec(v_val_623_);
v___x_633_ = lean_box(0);
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp___boxed(lean_object* v_transitions_635_, lean_object* v_timestamp_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_635_, v_timestamp_636_);
lean_dec_ref(v_timestamp_636_);
lean_dec_ref(v_transitions_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object* v_transitions_638_, lean_object* v_timestamp_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_638_, v_timestamp_639_);
if (lean_obj_tag(v___x_640_) == 1)
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_652_; 
v_val_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_652_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_array_get_size(v_transitions_638_);
v___x_646_ = lean_nat_dec_lt(v_val_641_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_del_object(v___x_643_);
lean_dec(v_val_641_);
v___x_647_ = lean_box(0);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_array_fget_borrowed(v_transitions_638_, v_val_641_);
lean_dec(v_val_641_);
lean_inc(v___x_648_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_648_);
v___x_650_ = v___x_643_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v___x_653_; 
lean_dec(v___x_640_);
v___x_653_ = lean_box(0);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp___boxed(lean_object* v_transitions_654_, lean_object* v_timestamp_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_654_, v_timestamp_655_);
lean_dec_ref(v_timestamp_655_);
lean_dec_ref(v_transitions_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object* v_transitions_660_, lean_object* v_tm_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_660_, v_tm_661_);
if (lean_obj_tag(v___x_662_) == 1)
{
lean_object* v_val_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_val_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_671_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_val_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_val_663_);
lean_dec(v_val_663_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v___x_672_; 
lean_dec(v___x_662_);
v___x_672_ = ((lean_object*)(l_Std_Time_TimeZone_Transition_timezoneAt___closed__1));
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt___boxed(lean_object* v_transitions_673_, lean_object* v_tm_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_673_, v_tm_674_);
lean_dec_ref(v_tm_674_);
lean_dec_ref(v_transitions_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds_spec__0(lean_object* v_a_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Rat_ofInt(v_a_676_);
return v___x_677_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(86400u);
v___x_679_ = lean_nat_to_int(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(lean_object* v_rule_680_, lean_object* v_year_681_, lean_object* v_wallOffset_682_){
_start:
{
lean_object* v_spec_683_; lean_object* v_time_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_spec_683_ = lean_ctor_get(v_rule_680_, 0);
lean_inc_ref(v_spec_683_);
v_time_684_ = lean_ctor_get(v_rule_680_, 1);
lean_inc(v_time_684_);
lean_dec_ref(v_rule_680_);
v___x_685_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDay(v_spec_683_, v_year_681_);
v___x_686_ = lean_obj_once(&l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0, &l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once, _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0);
v___x_687_ = lean_int_mul(v___x_685_, v___x_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_int_add(v___x_687_, v_time_684_);
lean_dec(v_time_684_);
lean_dec(v___x_687_);
v___x_689_ = lean_int_sub(v___x_688_, v_wallOffset_682_);
lean_dec(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___boxed(lean_object* v_rule_690_, lean_object* v_year_691_, lean_object* v_wallOffset_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_rule_690_, v_year_691_, v_wallOffset_692_);
lean_dec(v_wallOffset_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt(lean_object* v_rule_694_, lean_object* v_tm_695_){
_start:
{
lean_object* v_stdName_696_; lean_object* v_stdOffset_697_; lean_object* v_dst_698_; uint8_t v___x_699_; lean_object* v_stdTz_700_; 
v_stdName_696_ = lean_ctor_get(v_rule_694_, 0);
lean_inc_ref_n(v_stdName_696_, 2);
v_stdOffset_697_ = lean_ctor_get(v_rule_694_, 1);
lean_inc_n(v_stdOffset_697_, 2);
v_dst_698_ = lean_ctor_get(v_rule_694_, 2);
lean_inc(v_dst_698_);
lean_dec_ref(v_rule_694_);
v___x_699_ = 0;
v_stdTz_700_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_stdTz_700_, 0, v_stdOffset_697_);
lean_ctor_set(v_stdTz_700_, 1, v_stdName_696_);
lean_ctor_set(v_stdTz_700_, 2, v_stdName_696_);
lean_ctor_set_uint8(v_stdTz_700_, sizeof(void*)*3, v___x_699_);
if (lean_obj_tag(v_dst_698_) == 1)
{
lean_object* v_val_701_; lean_object* v_name_702_; lean_object* v_offset_703_; lean_object* v_start_704_; lean_object* v_end___705_; uint8_t v___x_706_; lean_object* v_dstTz_707_; 
v_val_701_ = lean_ctor_get(v_dst_698_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v_dst_698_, 1);
v_name_702_ = lean_ctor_get(v_val_701_, 0);
lean_inc_ref_n(v_name_702_, 2);
v_offset_703_ = lean_ctor_get(v_val_701_, 1);
lean_inc_n(v_offset_703_, 2);
v_start_704_ = lean_ctor_get(v_val_701_, 2);
lean_inc(v_start_704_);
v_end___705_ = lean_ctor_get(v_val_701_, 3);
lean_inc(v_end___705_);
lean_dec(v_val_701_);
v___x_706_ = 1;
v_dstTz_707_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_dstTz_707_, 0, v_offset_703_);
lean_ctor_set(v_dstTz_707_, 1, v_name_702_);
lean_ctor_set(v_dstTz_707_, 2, v_name_702_);
lean_ctor_set_uint8(v_dstTz_707_, sizeof(void*)*3, v___x_706_);
if (lean_obj_tag(v_start_704_) == 1)
{
if (lean_obj_tag(v_end___705_) == 1)
{
lean_object* v_val_708_; lean_object* v_val_709_; lean_object* v_second_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_year_714_; lean_object* v_dstStart_715_; lean_object* v_dstEnd_716_; uint8_t v___x_717_; 
v_val_708_ = lean_ctor_get(v_start_704_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v_start_704_, 1);
v_val_709_ = lean_ctor_get(v_end___705_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_end___705_, 1);
v_second_710_ = lean_ctor_get(v_tm_695_, 0);
v___x_711_ = lean_obj_once(&l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0, &l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once, _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0);
v___x_712_ = lean_int_ediv(v_second_710_, v___x_711_);
v___x_713_ = l_Std_Time_PlainDate_ofEpochDay(v___x_712_);
lean_dec(v___x_712_);
v_year_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc_n(v_year_714_, 2);
lean_dec_ref(v___x_713_);
v_dstStart_715_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_val_708_, v_year_714_, v_stdOffset_697_);
lean_dec(v_stdOffset_697_);
v_dstEnd_716_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_val_709_, v_year_714_, v_offset_703_);
lean_dec(v_offset_703_);
v___x_717_ = lean_int_dec_le(v_dstStart_715_, v_dstEnd_716_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; 
v___x_718_ = lean_int_dec_lt(v_second_710_, v_dstEnd_716_);
lean_dec(v_dstEnd_716_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = lean_int_dec_le(v_dstStart_715_, v_second_710_);
lean_dec(v_dstStart_715_);
if (v___x_719_ == 0)
{
lean_dec_ref_known(v_dstTz_707_, 3);
return v_stdTz_700_;
}
else
{
lean_dec_ref_known(v_stdTz_700_, 3);
return v_dstTz_707_;
}
}
else
{
lean_dec(v_dstStart_715_);
lean_dec_ref_known(v_stdTz_700_, 3);
return v_dstTz_707_;
}
}
else
{
uint8_t v___x_720_; 
v___x_720_ = lean_int_dec_le(v_dstStart_715_, v_second_710_);
lean_dec(v_dstStart_715_);
if (v___x_720_ == 0)
{
lean_dec(v_dstEnd_716_);
lean_dec_ref_known(v_dstTz_707_, 3);
return v_stdTz_700_;
}
else
{
uint8_t v___x_721_; 
v___x_721_ = lean_int_dec_lt(v_second_710_, v_dstEnd_716_);
lean_dec(v_dstEnd_716_);
if (v___x_721_ == 0)
{
lean_dec_ref_known(v_dstTz_707_, 3);
return v_stdTz_700_;
}
else
{
lean_dec_ref_known(v_stdTz_700_, 3);
return v_dstTz_707_;
}
}
}
}
else
{
lean_dec_ref_known(v_start_704_, 1);
lean_dec_ref_known(v_dstTz_707_, 3);
lean_dec(v_end___705_);
lean_dec(v_offset_703_);
lean_dec(v_stdOffset_697_);
return v_stdTz_700_;
}
}
else
{
lean_dec_ref_known(v_dstTz_707_, 3);
lean_dec(v_end___705_);
lean_dec(v_start_704_);
lean_dec(v_offset_703_);
lean_dec(v_stdOffset_697_);
return v_stdTz_700_;
}
}
else
{
lean_dec(v_dst_698_);
lean_dec(v_stdOffset_697_);
return v_stdTz_700_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt___boxed(lean_object* v_rule_722_, lean_object* v_tm_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_rule_722_, v_tm_723_);
lean_dec_ref(v_tm_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(lean_object* v_second_725_, lean_object* v_00___726_){
_start:
{
uint8_t v___x_727_; lean_object* v___x_728_; 
v___x_727_ = 1;
v___x_728_ = l_Std_Time_TimeZone_Offset_toIsoString(v_second_725_, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object* v_second_731_, lean_object* v_identifier_732_, lean_object* v_abbreviation_733_){
_start:
{
uint8_t v___x_734_; uint8_t v___y_736_; lean_object* v___y_737_; uint8_t v___y_738_; lean_object* v___y_739_; lean_object* v___y_745_; 
v___x_734_ = 0;
if (lean_obj_tag(v_abbreviation_733_) == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_box(0);
lean_inc(v_second_731_);
v___x_752_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(v_second_731_, v___x_751_);
v___y_745_ = v___x_752_;
goto v___jp_744_;
}
else
{
lean_object* v_val_753_; 
v_val_753_ = lean_ctor_get(v_abbreviation_733_, 0);
lean_inc(v_val_753_);
lean_dec_ref_known(v_abbreviation_733_, 1);
v___y_745_ = v_val_753_;
goto v___jp_744_;
}
v___jp_735_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_740_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_740_, 0, v_second_731_);
lean_ctor_set(v___x_740_, 1, v___y_737_);
lean_ctor_set(v___x_740_, 2, v___y_739_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*3, v___x_734_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*3 + 1, v___y_736_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*3 + 2, v___y_738_);
v___x_741_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0));
v___x_742_ = lean_box(0);
v___x_743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_743_, 0, v___x_740_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
return v___x_743_;
}
v___jp_744_:
{
uint8_t v___x_746_; uint8_t v___x_747_; 
v___x_746_ = 1;
v___x_747_ = 0;
if (lean_obj_tag(v_identifier_732_) == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_box(0);
lean_inc(v_second_731_);
v___x_749_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(v_second_731_, v___x_748_);
v___y_736_ = v___x_746_;
v___y_737_ = v___y_745_;
v___y_738_ = v___x_747_;
v___y_739_ = v___x_749_;
goto v___jp_735_;
}
else
{
lean_object* v_val_750_; 
v_val_750_ = lean_ctor_get(v_identifier_732_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v_identifier_732_, 1);
v___y_736_ = v___x_746_;
v___y_737_ = v___y_745_;
v___y_738_ = v___x_747_;
v___y_739_ = v_val_750_;
goto v___jp_735_;
}
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = lean_nat_to_int(v___x_754_);
return v___x_755_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_UTC___closed__2));
v___x_760_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_UTC___closed__0, &l_Std_Time_TimeZone_ZoneRules_UTC___closed__0_once, _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0);
v___x_761_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_760_, v___x_759_, v___x_759_);
return v___x_761_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC(void){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_UTC___closed__3, &l_Std_Time_TimeZone_ZoneRules_UTC___closed__3_once, _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(lean_object* v_zr_763_, lean_object* v_timestamp_764_){
_start:
{
lean_object* v_initialLocalTimeType_765_; lean_object* v_transitions_766_; lean_object* v_transitionRule_767_; lean_object* v___x_768_; 
v_initialLocalTimeType_765_ = lean_ctor_get(v_zr_763_, 0);
lean_inc_ref(v_initialLocalTimeType_765_);
v_transitions_766_ = lean_ctor_get(v_zr_763_, 1);
lean_inc_ref(v_transitions_766_);
v_transitionRule_767_ = lean_ctor_get(v_zr_763_, 2);
lean_inc(v_transitionRule_767_);
lean_dec_ref(v_zr_763_);
v___x_768_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_766_, v_timestamp_764_);
if (lean_obj_tag(v___x_768_) == 1)
{
lean_object* v_val_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = lean_array_get_size(v_transitions_766_);
v___x_771_ = lean_nat_dec_lt(v_val_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v_val_769_);
lean_dec(v_transitionRule_767_);
lean_dec_ref(v_transitions_766_);
return v_initialLocalTimeType_765_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
lean_dec_ref(v_initialLocalTimeType_765_);
v___x_772_ = lean_array_fget(v_transitions_766_, v_val_769_);
lean_dec_ref(v_transitions_766_);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_val_769_, v___x_773_);
lean_dec(v_val_769_);
v___x_775_ = lean_nat_dec_eq(v___x_774_, v___x_770_);
lean_dec(v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v_localTimeType_776_; 
lean_dec(v_transitionRule_767_);
v_localTimeType_776_ = lean_ctor_get(v___x_772_, 1);
lean_inc_ref(v_localTimeType_776_);
lean_dec(v___x_772_);
return v_localTimeType_776_;
}
else
{
if (lean_obj_tag(v_transitionRule_767_) == 1)
{
lean_object* v_val_777_; lean_object* v_localTimeType_778_; lean_object* v_tz_779_; lean_object* v_offset_780_; lean_object* v_name_781_; lean_object* v_abbreviation_782_; uint8_t v_isDST_783_; uint8_t v_wall_784_; uint8_t v_utLocal_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_val_777_ = lean_ctor_get(v_transitionRule_767_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v_transitionRule_767_, 1);
v_localTimeType_778_ = lean_ctor_get(v___x_772_, 1);
lean_inc_ref(v_localTimeType_778_);
lean_dec(v___x_772_);
v_tz_779_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_val_777_, v_timestamp_764_);
v_offset_780_ = lean_ctor_get(v_tz_779_, 0);
lean_inc(v_offset_780_);
v_name_781_ = lean_ctor_get(v_tz_779_, 1);
lean_inc_ref(v_name_781_);
v_abbreviation_782_ = lean_ctor_get(v_tz_779_, 2);
lean_inc_ref(v_abbreviation_782_);
v_isDST_783_ = lean_ctor_get_uint8(v_tz_779_, sizeof(void*)*3);
lean_dec_ref(v_tz_779_);
v_wall_784_ = lean_ctor_get_uint8(v_localTimeType_778_, sizeof(void*)*3 + 1);
v_utLocal_785_ = lean_ctor_get_uint8(v_localTimeType_778_, sizeof(void*)*3 + 2);
v_isSharedCheck_792_ = !lean_is_exclusive(v_localTimeType_778_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; lean_object* v_unused_794_; lean_object* v_unused_795_; 
v_unused_793_ = lean_ctor_get(v_localTimeType_778_, 2);
lean_dec(v_unused_793_);
v_unused_794_ = lean_ctor_get(v_localTimeType_778_, 1);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_localTimeType_778_, 0);
lean_dec(v_unused_795_);
v___x_787_ = v_localTimeType_778_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_dec(v_localTimeType_778_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v_name_781_);
lean_ctor_set(v___x_787_, 1, v_abbreviation_782_);
lean_ctor_set(v___x_787_, 0, v_offset_780_);
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_offset_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_abbreviation_782_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_name_781_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*3 + 1, v_wall_784_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*3 + 2, v_utLocal_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_ctor_set_uint8(v___x_790_, sizeof(void*)*3, v_isDST_783_);
return v___x_790_;
}
}
}
else
{
lean_object* v_localTimeType_796_; 
lean_dec(v_transitionRule_767_);
v_localTimeType_796_ = lean_ctor_get(v___x_772_, 1);
lean_inc_ref(v_localTimeType_796_);
lean_dec(v___x_772_);
return v_localTimeType_796_;
}
}
}
}
else
{
lean_dec(v___x_768_);
lean_dec(v_transitionRule_767_);
lean_dec_ref(v_transitions_766_);
return v_initialLocalTimeType_765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp___boxed(lean_object* v_zr_797_, lean_object* v_timestamp_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_797_, v_timestamp_798_);
lean_dec_ref(v_timestamp_798_);
return v_res_799_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(1000000000u);
v___x_801_ = lean_nat_to_int(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(lean_object* v_wallTime_802_, lean_object* v_as_803_, size_t v_sz_804_, size_t v_i_805_, lean_object* v_b_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = lean_usize_dec_lt(v_i_805_, v_sz_804_);
if (v___x_807_ == 0)
{
return v_b_806_;
}
else
{
lean_object* v_snd_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_838_; 
v_snd_808_ = lean_ctor_get(v_b_806_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_806_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_b_806_, 0);
lean_dec(v_unused_839_);
v___x_810_ = v_b_806_;
v_isShared_811_ = v_isSharedCheck_838_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_snd_808_);
lean_dec(v_b_806_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_838_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_gmtOffset_812_; lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v_second_815_; lean_object* v_nano_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_gmtOffset_812_ = lean_ctor_get(v_snd_808_, 0);
v_a_813_ = lean_array_uget_borrowed(v_as_803_, v_i_805_);
lean_inc(v_a_813_);
v___x_814_ = l_Std_Time_TimeZone_Transition_timestamp(v_a_813_);
v_second_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_second_815_);
v_nano_816_ = lean_ctor_get(v___x_814_, 1);
lean_inc(v_nano_816_);
lean_dec_ref(v___x_814_);
v___x_817_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_818_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0);
v___x_819_ = lean_int_mul(v_second_815_, v___x_818_);
lean_dec(v_second_815_);
v___x_820_ = lean_int_add(v___x_819_, v_nano_816_);
lean_dec(v_nano_816_);
lean_dec(v___x_819_);
v___x_821_ = lean_int_mul(v_gmtOffset_812_, v___x_818_);
v___x_822_ = lean_int_add(v___x_821_, v___x_817_);
lean_dec(v___x_821_);
v___x_823_ = lean_int_add(v___x_820_, v___x_822_);
lean_dec(v___x_822_);
lean_dec(v___x_820_);
v___x_824_ = l_Std_Time_Duration_ofNanoseconds(v___x_823_);
lean_dec(v___x_823_);
v___x_825_ = l_Std_Time_Duration_instDecidableLt(v_wallTime_802_, v___x_824_);
lean_dec_ref(v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v_localTimeType_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_snd_808_);
v_localTimeType_826_ = lean_ctor_get(v_a_813_, 1);
v___x_827_ = lean_box(0);
lean_inc_ref(v_localTimeType_826_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 1, v_localTimeType_826_);
lean_ctor_set(v___x_810_, 0, v___x_827_);
v___x_829_ = v___x_810_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_localTimeType_826_);
v___x_829_ = v_reuseFailAlloc_833_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
size_t v___x_830_; size_t v___x_831_; 
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_add(v_i_805_, v___x_830_);
v_i_805_ = v___x_831_;
v_b_806_ = v___x_829_;
goto _start;
}
}
else
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_inc(v_snd_808_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_snd_808_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_834_);
v___x_836_ = v___x_810_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_snd_808_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___boxed(lean_object* v_wallTime_840_, lean_object* v_as_841_, lean_object* v_sz_842_, lean_object* v_i_843_, lean_object* v_b_844_){
_start:
{
size_t v_sz_boxed_845_; size_t v_i_boxed_846_; lean_object* v_res_847_; 
v_sz_boxed_845_ = lean_unbox_usize(v_sz_842_);
lean_dec(v_sz_842_);
v_i_boxed_846_ = lean_unbox_usize(v_i_843_);
lean_dec(v_i_843_);
v_res_847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_840_, v_as_841_, v_sz_boxed_845_, v_i_boxed_846_, v_b_844_);
lean_dec_ref(v_as_841_);
lean_dec_ref(v_wallTime_840_);
return v_res_847_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_849_ = lean_int_neg(v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object* v_zr_850_, lean_object* v_wallTime_851_){
_start:
{
lean_object* v_initialLocalTimeType_852_; lean_object* v_transitions_853_; lean_object* v_transitionRule_854_; lean_object* v___x_855_; lean_object* v___x_856_; size_t v_sz_857_; size_t v___x_858_; lean_object* v___x_859_; lean_object* v_fst_860_; 
v_initialLocalTimeType_852_ = lean_ctor_get(v_zr_850_, 0);
lean_inc_ref(v_initialLocalTimeType_852_);
v_transitions_853_ = lean_ctor_get(v_zr_850_, 1);
lean_inc_ref(v_transitions_853_);
v_transitionRule_854_ = lean_ctor_get(v_zr_850_, 2);
lean_inc(v_transitionRule_854_);
lean_dec_ref(v_zr_850_);
v___x_855_ = lean_box(0);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_initialLocalTimeType_852_);
v_sz_857_ = lean_array_size(v_transitions_853_);
v___x_858_ = ((size_t)0ULL);
v___x_859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_851_, v_transitions_853_, v_sz_857_, v___x_858_, v___x_856_);
lean_dec_ref(v_transitions_853_);
v_fst_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_fst_860_);
if (lean_obj_tag(v_fst_860_) == 0)
{
if (lean_obj_tag(v_transitionRule_854_) == 1)
{
lean_object* v_snd_861_; lean_object* v_val_862_; lean_object* v_gmtOffset_863_; uint8_t v_wall_864_; uint8_t v_utLocal_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_888_; 
v_snd_861_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_snd_861_);
lean_dec_ref(v___x_859_);
v_val_862_ = lean_ctor_get(v_transitionRule_854_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_transitionRule_854_, 1);
v_gmtOffset_863_ = lean_ctor_get(v_snd_861_, 0);
v_wall_864_ = lean_ctor_get_uint8(v_snd_861_, sizeof(void*)*3 + 1);
v_utLocal_865_ = lean_ctor_get_uint8(v_snd_861_, sizeof(void*)*3 + 2);
v_isSharedCheck_888_ = !lean_is_exclusive(v_snd_861_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; lean_object* v_unused_890_; 
v_unused_889_ = lean_ctor_get(v_snd_861_, 2);
lean_dec(v_unused_889_);
v_unused_890_ = lean_ctor_get(v_snd_861_, 1);
lean_dec(v_unused_890_);
v___x_867_ = v_snd_861_;
v_isShared_868_ = v_isSharedCheck_888_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_gmtOffset_863_);
lean_dec(v_snd_861_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_888_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_second_869_; lean_object* v_nano_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_offset_881_; lean_object* v_name_882_; lean_object* v_abbreviation_883_; uint8_t v_isDST_884_; lean_object* v___x_886_; 
v_second_869_ = lean_ctor_get(v_wallTime_851_, 0);
v_nano_870_ = lean_ctor_get(v_wallTime_851_, 1);
v___x_871_ = lean_int_neg(v_gmtOffset_863_);
lean_dec(v_gmtOffset_863_);
v___x_872_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0, &l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0_once, _init_l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0);
v___x_873_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___closed__0);
v___x_874_ = lean_int_mul(v_second_869_, v___x_873_);
v___x_875_ = lean_int_add(v___x_874_, v_nano_870_);
lean_dec(v___x_874_);
v___x_876_ = lean_int_mul(v___x_871_, v___x_873_);
lean_dec(v___x_871_);
v___x_877_ = lean_int_add(v___x_876_, v___x_872_);
lean_dec(v___x_876_);
v___x_878_ = lean_int_add(v___x_875_, v___x_877_);
lean_dec(v___x_877_);
lean_dec(v___x_875_);
v___x_879_ = l_Std_Time_Duration_ofNanoseconds(v___x_878_);
lean_dec(v___x_878_);
v___x_880_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_val_862_, v___x_879_);
lean_dec_ref(v___x_879_);
v_offset_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_offset_881_);
v_name_882_ = lean_ctor_get(v___x_880_, 1);
lean_inc_ref(v_name_882_);
v_abbreviation_883_ = lean_ctor_get(v___x_880_, 2);
lean_inc_ref(v_abbreviation_883_);
v_isDST_884_ = lean_ctor_get_uint8(v___x_880_, sizeof(void*)*3);
lean_dec_ref(v___x_880_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 2, v_name_882_);
lean_ctor_set(v___x_867_, 1, v_abbreviation_883_);
lean_ctor_set(v___x_867_, 0, v_offset_881_);
v___x_886_ = v___x_867_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_offset_881_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_abbreviation_883_);
lean_ctor_set(v_reuseFailAlloc_887_, 2, v_name_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_887_, sizeof(void*)*3 + 1, v_wall_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_887_, sizeof(void*)*3 + 2, v_utLocal_865_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*3, v_isDST_884_);
return v___x_886_;
}
}
}
else
{
lean_object* v_snd_891_; 
lean_dec(v_transitionRule_854_);
v_snd_891_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_snd_891_);
lean_dec_ref(v___x_859_);
return v_snd_891_;
}
}
else
{
lean_object* v_val_892_; 
lean_dec_ref(v___x_859_);
lean_dec(v_transitionRule_854_);
v_val_892_ = lean_ctor_get(v_fst_860_, 0);
lean_inc(v_val_892_);
lean_dec_ref_known(v_fst_860_, 1);
return v_val_892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___boxed(lean_object* v_zr_893_, lean_object* v_wallTime_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_893_, v_wallTime_894_);
lean_dec_ref(v_wallTime_894_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object* v_zr_896_, lean_object* v_tm_897_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_896_, v_tm_897_);
v___x_899_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_898_);
lean_dec_ref(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt___boxed(lean_object* v_zr_900_, lean_object* v_tm_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_zr_900_, v_tm_901_);
lean_dec_ref(v_tm_901_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone(lean_object* v_tz_903_){
_start:
{
lean_object* v_offset_904_; lean_object* v_name_905_; lean_object* v_abbreviation_906_; uint8_t v_isDST_907_; uint8_t v___x_908_; uint8_t v___x_909_; lean_object* v_ltt_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_offset_904_ = lean_ctor_get(v_tz_903_, 0);
v_name_905_ = lean_ctor_get(v_tz_903_, 1);
v_abbreviation_906_ = lean_ctor_get(v_tz_903_, 2);
v_isDST_907_ = lean_ctor_get_uint8(v_tz_903_, sizeof(void*)*3);
v___x_908_ = 0;
v___x_909_ = 1;
lean_inc_ref(v_name_905_);
lean_inc_ref(v_abbreviation_906_);
lean_inc(v_offset_904_);
v_ltt_910_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_910_, 0, v_offset_904_);
lean_ctor_set(v_ltt_910_, 1, v_abbreviation_906_);
lean_ctor_set(v_ltt_910_, 2, v_name_905_);
lean_ctor_set_uint8(v_ltt_910_, sizeof(void*)*3, v_isDST_907_);
lean_ctor_set_uint8(v_ltt_910_, sizeof(void*)*3 + 1, v___x_908_);
lean_ctor_set_uint8(v_ltt_910_, sizeof(void*)*3 + 2, v___x_909_);
v___x_911_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0));
v___x_912_ = lean_box(0);
v___x_913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_913_, 0, v_ltt_910_);
lean_ctor_set(v___x_913_, 1, v___x_911_);
lean_ctor_set(v___x_913_, 2, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone___boxed(lean_object* v_tz_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_Time_TimeZone_ZoneRules_ofTimeZone(v_tz_914_);
lean_dec_ref(v_tz_914_);
return v_res_915_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_RecurringRule(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
