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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx___impl___boxed(lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_Time_TimeZone_UTLocal_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_UTLocal_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Time_TimeZone_UTLocal_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Time_TimeZone_UTLocal_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Time_TimeZone_UTLocal_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_UTLocal_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Time_TimeZone_UTLocal_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Time_TimeZone_UTLocal_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(lean_object* v_ut_24_){
_start:
{
lean_inc(v_ut_24_);
return v_ut_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___redArg___boxed(lean_object* v_ut_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_TimeZone_UTLocal_ut_elim___redArg(v_ut_25_);
lean_dec(v_ut_25_);
return v_res_26_;
}
}
lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_ut_30_){
_start:
{
lean_inc(v_ut_30_);
return v_ut_30_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_UTLocal_ut_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_ut_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Time_TimeZone_UTLocal_ut_elim(lean_box(0), v_t_28_, lean_box(0), v_ut_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_ut_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_ut_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Time_TimeZone_UTLocal_ut_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_ut_35_);
lean_dec(v_ut_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___redArg(lean_object* v_local_38_){
_start:
{
lean_inc(v_local_38_);
return v_local_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___redArg___boxed(lean_object* v_local_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Time_TimeZone_UTLocal_local_elim___redArg(v_local_39_);
lean_dec(v_local_39_);
return v_res_40_;
}
}
lean_object* l_Std_Time_TimeZone_UTLocal_local_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_local_44_){
_start:
{
lean_inc(v_local_44_);
return v_local_44_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_UTLocal_local_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_local_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Time_TimeZone_UTLocal_local_elim(lean_box(0), v_t_42_, lean_box(0), v_local_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTLocal_local_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_local_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Time_TimeZone_UTLocal_local_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_local_49_);
lean_dec(v_local_49_);
return v_res_51_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(2u);
v___x_59_ = lean_nat_to_int(v___x_58_);
return v___x_59_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr(uint8_t v_x_62_, lean_object* v_prec_63_){
_start:
{
lean_object* v___y_65_; lean_object* v___y_72_; 
if (v_x_62_ == 0)
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1024u);
v___x_79_ = lean_nat_dec_le(v___x_78_, v_prec_63_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_65_ = v___x_80_;
goto v___jp_64_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_65_ = v___x_81_;
goto v___jp_64_;
}
}
else
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1024u);
v___x_83_ = lean_nat_dec_le(v___x_82_, v_prec_63_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_72_ = v___x_84_;
goto v___jp_71_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_72_ = v___x_85_;
goto v___jp_71_;
}
}
v___jp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_66_ = ((lean_object*)(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__1));
lean_inc(v___y_65_);
v___x_67_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_67_, 0, v___y_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = 0;
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_68_);
v___x_70_ = l_Repr_addAppParen(v___x_69_, v_prec_63_);
return v___x_70_;
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = ((lean_object*)(l_Std_Time_TimeZone_instReprUTLocal_repr___closed__3));
lean_inc(v___y_72_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = 0;
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = l_Repr_addAppParen(v___x_76_, v_prec_63_);
return v___x_77_;
}
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_instReprUTLocal_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_62_ = stack[0].m_num;
lean_object* v_prec_63_ = stack[1].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_x_62_, v_prec_63_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprUTLocal_repr___boxed(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
uint8_t v_x_117__boxed_89_; lean_object* v_res_90_; 
v_x_117__boxed_89_ = lean_unbox(v_x_87_);
v_res_90_ = l_Std_Time_TimeZone_instReprUTLocal_repr(v_x_117__boxed_89_, v_prec_88_);
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
lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx___impl(uint8_t v_x_95_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_box(v_x_95_);
v___x_97_ = lean_obj_tag_nat(v___x_96_);
lean_dec(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_StdWall_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_95_ = stack[0].m_num;
lean_object* v_res_98_;
v_res_98_ = l_Std_Time_TimeZone_StdWall_ctorIdx___impl(v_x_95_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorIdx___impl___boxed(lean_object* v_x_99_){
_start:
{
uint8_t v_x_4__boxed_100_; lean_object* v_res_101_; 
v_x_4__boxed_100_ = lean_unbox(v_x_99_);
v_res_101_ = l_Std_Time_TimeZone_StdWall_ctorIdx___impl(v_x_4__boxed_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___redArg(lean_object* v_k_102_){
_start:
{
lean_inc(v_k_102_);
return v_k_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___redArg___boxed(lean_object* v_k_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_Time_TimeZone_StdWall_ctorElim___redArg(v_k_103_);
lean_dec(v_k_103_);
return v_res_104_;
}
}
lean_object* l_Std_Time_TimeZone_StdWall_ctorElim(lean_object* v_motive_105_, lean_object* v_ctorIdx_106_, uint8_t v_t_107_, lean_object* v_h_108_, lean_object* v_k_109_){
_start:
{
lean_inc(v_k_109_);
return v_k_109_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_StdWall_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_106_ = stack[1].m_obj;
uint8_t v_t_107_ = stack[2].m_num;
lean_object* v_k_109_ = stack[4].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_Std_Time_TimeZone_StdWall_ctorElim(lean_box(0), v_ctorIdx_106_, v_t_107_, lean_box(0), v_k_109_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_ctorElim___boxed(lean_object* v_motive_111_, lean_object* v_ctorIdx_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_k_115_){
_start:
{
uint8_t v_t_boxed_116_; lean_object* v_res_117_; 
v_t_boxed_116_ = lean_unbox(v_t_113_);
v_res_117_ = l_Std_Time_TimeZone_StdWall_ctorElim(v_motive_111_, v_ctorIdx_112_, v_t_boxed_116_, v_h_114_, v_k_115_);
lean_dec(v_k_115_);
lean_dec(v_ctorIdx_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___redArg(lean_object* v_wall_118_){
_start:
{
lean_inc(v_wall_118_);
return v_wall_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___redArg___boxed(lean_object* v_wall_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Time_TimeZone_StdWall_wall_elim___redArg(v_wall_119_);
lean_dec(v_wall_119_);
return v_res_120_;
}
}
lean_object* l_Std_Time_TimeZone_StdWall_wall_elim(lean_object* v_motive_121_, uint8_t v_t_122_, lean_object* v_h_123_, lean_object* v_wall_124_){
_start:
{
lean_inc(v_wall_124_);
return v_wall_124_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_StdWall_wall_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_122_ = stack[1].m_num;
lean_object* v_wall_124_ = stack[3].m_obj;
lean_object* v_res_125_;
v_res_125_ = l_Std_Time_TimeZone_StdWall_wall_elim(lean_box(0), v_t_122_, lean_box(0), v_wall_124_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_wall_elim___boxed(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_wall_129_){
_start:
{
uint8_t v_t_boxed_130_; lean_object* v_res_131_; 
v_t_boxed_130_ = lean_unbox(v_t_127_);
v_res_131_ = l_Std_Time_TimeZone_StdWall_wall_elim(v_motive_126_, v_t_boxed_130_, v_h_128_, v_wall_129_);
lean_dec(v_wall_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___redArg(lean_object* v_standard_132_){
_start:
{
lean_inc(v_standard_132_);
return v_standard_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___redArg___boxed(lean_object* v_standard_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_Time_TimeZone_StdWall_standard_elim___redArg(v_standard_133_);
lean_dec(v_standard_133_);
return v_res_134_;
}
}
lean_object* l_Std_Time_TimeZone_StdWall_standard_elim(lean_object* v_motive_135_, uint8_t v_t_136_, lean_object* v_h_137_, lean_object* v_standard_138_){
_start:
{
lean_inc(v_standard_138_);
return v_standard_138_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_StdWall_standard_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_136_ = stack[1].m_num;
lean_object* v_standard_138_ = stack[3].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Std_Time_TimeZone_StdWall_standard_elim(lean_box(0), v_t_136_, lean_box(0), v_standard_138_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_StdWall_standard_elim___boxed(lean_object* v_motive_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_standard_143_){
_start:
{
uint8_t v_t_boxed_144_; lean_object* v_res_145_; 
v_t_boxed_144_ = lean_unbox(v_t_141_);
v_res_145_ = l_Std_Time_TimeZone_StdWall_standard_elim(v_motive_140_, v_t_boxed_144_, v_h_142_, v_standard_143_);
lean_dec(v_standard_143_);
return v_res_145_;
}
}
lean_object* l_Std_Time_TimeZone_instReprStdWall_repr(uint8_t v_x_152_, lean_object* v_prec_153_){
_start:
{
lean_object* v___y_155_; lean_object* v___y_162_; 
if (v_x_152_ == 0)
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(1024u);
v___x_169_ = lean_nat_dec_le(v___x_168_, v_prec_153_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_155_ = v___x_170_;
goto v___jp_154_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_155_ = v___x_171_;
goto v___jp_154_;
}
}
else
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_153_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__4);
v___y_162_ = v___x_174_;
goto v___jp_161_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5, &l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5_once, _init_l_Std_Time_TimeZone_instReprUTLocal_repr___closed__5);
v___y_162_ = v___x_175_;
goto v___jp_161_;
}
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = ((lean_object*)(l_Std_Time_TimeZone_instReprStdWall_repr___closed__1));
lean_inc(v___y_155_);
v___x_157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_157_, 0, v___y_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = 0;
v___x_159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_158_);
v___x_160_ = l_Repr_addAppParen(v___x_159_, v_prec_153_);
return v___x_160_;
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_163_ = ((lean_object*)(l_Std_Time_TimeZone_instReprStdWall_repr___closed__3));
lean_inc(v___y_162_);
v___x_164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_164_, 0, v___y_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_165_);
v___x_167_ = l_Repr_addAppParen(v___x_166_, v_prec_153_);
return v___x_167_;
}
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_instReprStdWall_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_152_ = stack[0].m_num;
lean_object* v_prec_153_ = stack[1].m_obj;
lean_object* v_res_176_;
v_res_176_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_x_152_, v_prec_153_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprStdWall_repr___boxed(lean_object* v_x_177_, lean_object* v_prec_178_){
_start:
{
uint8_t v_x_113__boxed_179_; lean_object* v_res_180_; 
v_x_113__boxed_179_ = lean_unbox(v_x_177_);
v_res_180_ = l_Std_Time_TimeZone_instReprStdWall_repr(v_x_113__boxed_179_, v_prec_178_);
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
lean_object* v___x_405_; 
v___x_405_ = l_Std_Time_Internal_instInhabitedUnitVal_default___redArg();
return v___x_405_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v___x_407_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0, &l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__0);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition_default(void){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1, &l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1_once, _init_l_Std_Time_TimeZone_instInhabitedTransition_default___closed__1);
return v___x_409_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedTransition(void){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_Time_TimeZone_instInhabitedTransition_default;
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_object* v___x_419_; 
v___x_419_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__1));
return v___x_419_;
}
else
{
lean_object* v_val_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_val_420_ = lean_ctor_get(v_x_417_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_x_417_, 1);
v___x_421_ = ((lean_object*)(l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___closed__3));
v___x_422_ = l_Std_Time_TimeZone_instReprRecurringRule_repr___redArg(v_val_420_);
v___x_423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = l_Repr_addAppParen(v___x_423_, v_x_418_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1___boxed(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(v_x_425_, v_x_426_);
lean_dec(v_x_426_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_dec(v_x_428_);
return v_x_429_;
}
else
{
lean_object* v_head_431_; lean_object* v_tail_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_442_; 
v_head_431_ = lean_ctor_get(v_x_430_, 0);
v_tail_432_ = lean_ctor_get(v_x_430_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_442_ == 0)
{
v___x_434_ = v_x_430_;
v_isShared_435_ = v_isSharedCheck_442_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_tail_432_);
lean_inc(v_head_431_);
lean_dec(v_x_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_442_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
lean_inc(v_x_428_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 5);
lean_ctor_set(v___x_434_, 1, v_x_428_);
lean_ctor_set(v___x_434_, 0, v_x_429_);
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_x_429_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_x_428_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_431_);
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v_x_429_ = v___x_439_;
v_x_430_ = v_tail_432_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_dec(v_x_443_);
return v_x_444_;
}
else
{
lean_object* v_head_446_; lean_object* v_tail_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_457_; 
v_head_446_ = lean_ctor_get(v_x_445_, 0);
v_tail_447_ = lean_ctor_get(v_x_445_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_457_ == 0)
{
v___x_449_ = v_x_445_;
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_tail_447_);
lean_inc(v_head_446_);
lean_dec(v_x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
lean_inc(v_x_443_);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 5);
lean_ctor_set(v___x_449_, 1, v_x_443_);
lean_ctor_set(v___x_449_, 0, v_x_444_);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_x_444_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_x_443_);
v___x_452_ = v_reuseFailAlloc_456_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_446_);
v___x_454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2_spec__3(v_x_443_, v___x_454_, v_tail_447_);
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v___x_460_; 
lean_dec(v_x_459_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v_tail_461_; 
v_tail_461_ = lean_ctor_get(v_x_458_, 1);
if (lean_obj_tag(v_tail_461_) == 0)
{
lean_object* v_head_462_; lean_object* v___x_463_; 
lean_dec(v_x_459_);
v_head_462_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_head_462_);
lean_dec_ref_known(v_x_458_, 2);
v___x_463_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_462_);
return v___x_463_;
}
else
{
lean_object* v_head_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc(v_tail_461_);
v_head_464_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_head_464_);
lean_dec_ref_known(v_x_458_, 2);
v___x_465_ = l_Std_Time_TimeZone_instReprTransition_repr___redArg(v_head_464_);
v___x_466_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0_spec__2(v_x_459_, v___x_465_, v_tail_461_);
return v___x_466_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__0));
v___x_473_ = lean_string_length(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3, &l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3_once, _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__3);
v___x_475_ = lean_nat_to_int(v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(lean_object* v_xs_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_484_ = lean_array_get_size(v_xs_483_);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_nat_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_487_ = lean_array_to_list(v_xs_483_);
v___x_488_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__1));
v___x_489_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0_spec__0(v___x_487_, v___x_488_);
v___x_490_ = lean_obj_once(&l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4, &l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4_once, _init_l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__4);
v___x_491_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__5));
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_489_);
v___x_493_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__6));
v___x_494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_490_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l_Std_Format_fill(v___x_495_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; 
lean_dec_ref(v_xs_483_);
v___x_497_ = ((lean_object*)(l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0___closed__8));
return v___x_497_;
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(24u);
v___x_508_ = lean_nat_to_int(v___x_507_);
return v___x_508_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(15u);
v___x_513_ = lean_nat_to_int(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(18u);
v___x_518_ = lean_nat_to_int(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(lean_object* v_x_519_){
_start:
{
lean_object* v_initialLocalTimeType_520_; lean_object* v_transitions_521_; lean_object* v_transitionRule_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_initialLocalTimeType_520_ = lean_ctor_get(v_x_519_, 0);
lean_inc_ref(v_initialLocalTimeType_520_);
v_transitions_521_ = lean_ctor_get(v_x_519_, 1);
lean_inc_ref(v_transitions_521_);
v_transitionRule_522_ = lean_ctor_get(v_x_519_, 2);
lean_inc(v_transitionRule_522_);
lean_dec_ref(v_x_519_);
v___x_523_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__5));
v___x_524_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__3));
v___x_525_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__4);
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg(v_initialLocalTimeType_520_);
v___x_528_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_525_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = 0;
v___x_530_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*1, v___x_529_);
v___x_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_524_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__9));
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_box(1);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__6));
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_523_);
v___x_539_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__7);
v___x_540_ = l_Array_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__0(v_transitions_521_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_529_);
v___x_543_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_538_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v___x_532_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_534_);
v___x_546_ = ((lean_object*)(l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__9));
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_545_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_523_);
v___x_549_ = lean_obj_once(&l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10, &l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_instReprZoneRules_repr___redArg___closed__10);
v___x_550_ = l_Option_repr___at___00Std_Time_TimeZone_instReprZoneRules_repr_spec__1(v_transitionRule_522_, v___x_526_);
v___x_551_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_552_, 0, v___x_551_);
lean_ctor_set_uint8(v___x_552_, sizeof(void*)*1, v___x_529_);
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_548_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_obj_once(&l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27, &l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27_once, _init_l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__27);
v___x_555_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__28));
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_553_);
v___x_557_ = ((lean_object*)(l_Std_Time_TimeZone_instReprLocalTimeType_repr___redArg___closed__29));
v___x_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_554_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set_uint8(v___x_560_, sizeof(void*)*1, v___x_529_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr(lean_object* v_x_561_, lean_object* v_prec_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_Time_TimeZone_instReprZoneRules_repr___redArg(v_x_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprZoneRules_repr___boxed(lean_object* v_x_564_, lean_object* v_prec_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_Time_TimeZone_instReprZoneRules_repr(v_x_564_, v_prec_565_);
lean_dec(v_prec_565_);
return v_res_566_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_571_ = lean_box(0);
v___x_572_ = ((lean_object*)(l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__0));
v___x_573_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
v___x_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
lean_ctor_set(v___x_574_, 2, v___x_571_);
return v___x_574_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1, &l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1_once, _init_l_Std_Time_TimeZone_instInhabitedZoneRules_default___closed__1);
return v___x_575_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedZoneRules(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timestamp(lean_object* v_t_577_){
_start:
{
lean_object* v_time_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
v_time_578_ = lean_ctor_get(v_t_577_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_t_577_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v_t_577_, 1);
lean_dec(v_unused_587_);
v___x_580_ = v_t_577_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_time_578_);
lean_dec(v_t_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_582_);
v___x_584_ = v___x_580_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_time_578_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(lean_object* v_transition_588_){
_start:
{
lean_object* v_localTimeType_589_; lean_object* v_gmtOffset_590_; uint8_t v_isDst_591_; lean_object* v_abbreviation_592_; lean_object* v_identifier_593_; lean_object* v___x_594_; 
v_localTimeType_589_ = lean_ctor_get(v_transition_588_, 1);
v_gmtOffset_590_ = lean_ctor_get(v_localTimeType_589_, 0);
v_isDst_591_ = lean_ctor_get_uint8(v_localTimeType_589_, sizeof(void*)*3);
v_abbreviation_592_ = lean_ctor_get(v_localTimeType_589_, 1);
v_identifier_593_ = lean_ctor_get(v_localTimeType_589_, 2);
lean_inc_ref(v_abbreviation_592_);
lean_inc_ref(v_identifier_593_);
lean_inc(v_gmtOffset_590_);
v___x_594_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_594_, 0, v_gmtOffset_590_);
lean_ctor_set(v___x_594_, 1, v_identifier_593_);
lean_ctor_set(v___x_594_, 2, v_abbreviation_592_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*3, v_isDst_591_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition___boxed(lean_object* v_transition_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_transition_595_);
lean_dec_ref(v_transition_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(lean_object* v_value_597_, lean_object* v_as_598_, lean_object* v_j_599_){
_start:
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_get_size(v_as_598_);
v___x_601_ = lean_nat_dec_lt(v_j_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec(v_j_599_);
v___x_602_ = lean_box(0);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v_time_604_; uint8_t v___x_605_; 
v___x_603_ = lean_array_fget_borrowed(v_as_598_, v_j_599_);
v_time_604_ = lean_ctor_get(v___x_603_, 0);
v___x_605_ = lean_int_dec_lt(v_value_597_, v_time_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_j_599_, v___x_606_);
lean_dec(v_j_599_);
v_j_599_ = v___x_607_;
goto _start;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v_j_599_);
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0___boxed(lean_object* v_value_610_, lean_object* v_as_611_, lean_object* v_j_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_value_610_, v_as_611_, v_j_612_);
lean_dec_ref(v_as_611_);
lean_dec(v_value_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(lean_object* v_transitions_614_, lean_object* v_timestamp_615_){
_start:
{
lean_object* v_second_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_second_616_ = lean_ctor_get(v_timestamp_615_, 0);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = l_Array_findIdx_x3f_loop___at___00Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp_spec__0(v_second_616_, v_transitions_614_, v___x_617_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_array_get_size(v_transitions_614_);
v___x_620_ = lean_nat_dec_eq(v___x_619_, v___x_617_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_sub(v___x_619_, v___x_621_);
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
else
{
return v___x_618_;
}
}
else
{
lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_635_; 
v_val_624_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_635_ == 0)
{
v___x_626_ = v___x_618_;
v_isShared_627_ = v_isSharedCheck_635_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v___x_618_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_635_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_eq(v_val_624_, v___x_617_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_sub(v_val_624_, v___x_629_);
lean_dec(v_val_624_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_630_);
v___x_632_ = v___x_626_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
else
{
lean_object* v___x_634_; 
lean_del_object(v___x_626_);
lean_dec(v_val_624_);
v___x_634_ = lean_box(0);
return v___x_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp___boxed(lean_object* v_transitions_636_, lean_object* v_timestamp_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_636_, v_timestamp_637_);
lean_dec_ref(v_timestamp_637_);
lean_dec_ref(v_transitions_636_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(lean_object* v_transitions_639_, lean_object* v_timestamp_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_639_, v_timestamp_640_);
if (lean_obj_tag(v___x_641_) == 1)
{
lean_object* v_val_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_653_; 
v_val_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_653_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_val_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_array_get_size(v_transitions_639_);
v___x_647_ = lean_nat_dec_lt(v_val_642_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
lean_del_object(v___x_644_);
lean_dec(v_val_642_);
v___x_648_ = lean_box(0);
return v___x_648_;
}
else
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_array_fget_borrowed(v_transitions_639_, v_val_642_);
lean_dec(v_val_642_);
lean_inc(v___x_649_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_649_);
v___x_651_ = v___x_644_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v___x_654_; 
lean_dec(v___x_641_);
v___x_654_ = lean_box(0);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_findTransitionForTimestamp___boxed(lean_object* v_transitions_655_, lean_object* v_timestamp_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_655_, v_timestamp_656_);
lean_dec_ref(v_timestamp_656_);
lean_dec_ref(v_transitions_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object* v_transitions_661_, lean_object* v_tm_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_Time_TimeZone_Transition_findTransitionForTimestamp(v_transitions_661_, v_tm_662_);
if (lean_obj_tag(v___x_663_) == 1)
{
lean_object* v_val_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_672_; 
v_val_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_672_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_val_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_672_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_668_ = l_Std_Time_TimeZone_Transition_createTimeZoneFromTransition(v_val_664_);
lean_dec(v_val_664_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_668_);
v___x_670_ = v___x_666_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v___x_673_; 
lean_dec(v___x_663_);
v___x_673_ = ((lean_object*)(l_Std_Time_TimeZone_Transition_timezoneAt___closed__1));
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Transition_timezoneAt___boxed(lean_object* v_transitions_674_, lean_object* v_tm_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_674_, v_tm_675_);
lean_dec_ref(v_tm_675_);
lean_dec_ref(v_transitions_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds_spec__0(lean_object* v_a_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Rat_ofInt(v_a_677_);
return v___x_678_;
}
}
static lean_object* _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_unsigned_to_nat(86400u);
v___x_680_ = lean_nat_to_int(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(lean_object* v_rule_681_, lean_object* v_year_682_, lean_object* v_wallOffset_683_){
_start:
{
lean_object* v_spec_684_; lean_object* v_time_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_spec_684_ = lean_ctor_get(v_rule_681_, 0);
lean_inc_ref(v_spec_684_);
v_time_685_ = lean_ctor_get(v_rule_681_, 1);
lean_inc(v_time_685_);
lean_dec_ref(v_rule_681_);
v___x_686_ = l_Std_Time_TimeZone_TransitionSpec_toEpochDay(v_spec_684_, v_year_682_);
v___x_687_ = lean_obj_once(&l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0, &l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once, _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0);
v___x_688_ = lean_int_mul(v___x_686_, v___x_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_int_add(v___x_688_, v_time_685_);
lean_dec(v_time_685_);
lean_dec(v___x_688_);
v___x_690_ = lean_int_sub(v___x_689_, v_wallOffset_683_);
lean_dec(v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___boxed(lean_object* v_rule_691_, lean_object* v_year_692_, lean_object* v_wallOffset_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_rule_691_, v_year_692_, v_wallOffset_693_);
lean_dec(v_wallOffset_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt(lean_object* v_rule_695_, lean_object* v_tm_696_){
_start:
{
lean_object* v_stdName_697_; lean_object* v_stdOffset_698_; lean_object* v_dst_699_; uint8_t v___x_700_; lean_object* v_stdTz_701_; 
v_stdName_697_ = lean_ctor_get(v_rule_695_, 0);
lean_inc_ref_n(v_stdName_697_, 2);
v_stdOffset_698_ = lean_ctor_get(v_rule_695_, 1);
lean_inc_n(v_stdOffset_698_, 2);
v_dst_699_ = lean_ctor_get(v_rule_695_, 2);
lean_inc(v_dst_699_);
lean_dec_ref(v_rule_695_);
v___x_700_ = 0;
v_stdTz_701_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_stdTz_701_, 0, v_stdOffset_698_);
lean_ctor_set(v_stdTz_701_, 1, v_stdName_697_);
lean_ctor_set(v_stdTz_701_, 2, v_stdName_697_);
lean_ctor_set_uint8(v_stdTz_701_, sizeof(void*)*3, v___x_700_);
if (lean_obj_tag(v_dst_699_) == 1)
{
lean_object* v_val_702_; lean_object* v_name_703_; lean_object* v_offset_704_; lean_object* v_start_705_; lean_object* v_end___706_; uint8_t v___x_707_; lean_object* v_dstTz_708_; 
v_val_702_ = lean_ctor_get(v_dst_699_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v_dst_699_, 1);
v_name_703_ = lean_ctor_get(v_val_702_, 0);
lean_inc_ref_n(v_name_703_, 2);
v_offset_704_ = lean_ctor_get(v_val_702_, 1);
lean_inc_n(v_offset_704_, 2);
v_start_705_ = lean_ctor_get(v_val_702_, 2);
lean_inc(v_start_705_);
v_end___706_ = lean_ctor_get(v_val_702_, 3);
lean_inc(v_end___706_);
lean_dec(v_val_702_);
v___x_707_ = 1;
v_dstTz_708_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_dstTz_708_, 0, v_offset_704_);
lean_ctor_set(v_dstTz_708_, 1, v_name_703_);
lean_ctor_set(v_dstTz_708_, 2, v_name_703_);
lean_ctor_set_uint8(v_dstTz_708_, sizeof(void*)*3, v___x_707_);
if (lean_obj_tag(v_start_705_) == 1)
{
if (lean_obj_tag(v_end___706_) == 1)
{
lean_object* v_val_709_; lean_object* v_val_710_; lean_object* v_second_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_year_715_; lean_object* v_dstStart_716_; lean_object* v_dstEnd_717_; uint8_t v___x_718_; 
v_val_709_ = lean_ctor_get(v_start_705_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_start_705_, 1);
v_val_710_ = lean_ctor_get(v_end___706_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v_end___706_, 1);
v_second_711_ = lean_ctor_get(v_tm_696_, 0);
v___x_712_ = lean_obj_once(&l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0, &l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0_once, _init_l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds___closed__0);
v___x_713_ = lean_int_ediv(v_second_711_, v___x_712_);
v___x_714_ = l_Std_Time_PlainDate_ofEpochDay(v___x_713_);
lean_dec(v___x_713_);
v_year_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc_n(v_year_715_, 2);
lean_dec_ref(v___x_714_);
v_dstStart_716_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_val_709_, v_year_715_, v_stdOffset_698_);
lean_dec(v_stdOffset_698_);
v_dstEnd_717_ = l___private_Std_Time_Zoned_ZoneRules_0__Std_Time_TimeZone_RecurringRule_transitionUtcSeconds(v_val_710_, v_year_715_, v_offset_704_);
lean_dec(v_offset_704_);
v___x_718_ = lean_int_dec_le(v_dstStart_716_, v_dstEnd_717_);
if (v___x_718_ == 0)
{
uint8_t v___x_719_; 
v___x_719_ = lean_int_dec_lt(v_second_711_, v_dstEnd_717_);
lean_dec(v_dstEnd_717_);
if (v___x_719_ == 0)
{
uint8_t v___x_720_; 
v___x_720_ = lean_int_dec_le(v_dstStart_716_, v_second_711_);
lean_dec(v_dstStart_716_);
if (v___x_720_ == 0)
{
lean_dec_ref_known(v_dstTz_708_, 3);
return v_stdTz_701_;
}
else
{
lean_dec_ref_known(v_stdTz_701_, 3);
return v_dstTz_708_;
}
}
else
{
lean_dec(v_dstStart_716_);
lean_dec_ref_known(v_stdTz_701_, 3);
return v_dstTz_708_;
}
}
else
{
uint8_t v___x_721_; 
v___x_721_ = lean_int_dec_le(v_dstStart_716_, v_second_711_);
lean_dec(v_dstStart_716_);
if (v___x_721_ == 0)
{
lean_dec(v_dstEnd_717_);
lean_dec_ref_known(v_dstTz_708_, 3);
return v_stdTz_701_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = lean_int_dec_lt(v_second_711_, v_dstEnd_717_);
lean_dec(v_dstEnd_717_);
if (v___x_722_ == 0)
{
lean_dec_ref_known(v_dstTz_708_, 3);
return v_stdTz_701_;
}
else
{
lean_dec_ref_known(v_stdTz_701_, 3);
return v_dstTz_708_;
}
}
}
}
else
{
lean_dec_ref_known(v_start_705_, 1);
lean_dec_ref_known(v_dstTz_708_, 3);
lean_dec(v_end___706_);
lean_dec(v_offset_704_);
lean_dec(v_stdOffset_698_);
return v_stdTz_701_;
}
}
else
{
lean_dec_ref_known(v_dstTz_708_, 3);
lean_dec(v_end___706_);
lean_dec(v_start_705_);
lean_dec(v_offset_704_);
lean_dec(v_stdOffset_698_);
return v_stdTz_701_;
}
}
else
{
lean_dec(v_dst_699_);
lean_dec(v_stdOffset_698_);
return v_stdTz_701_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_RecurringRule_timezoneAt___boxed(lean_object* v_rule_723_, lean_object* v_tm_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_rule_723_, v_tm_724_);
lean_dec_ref(v_tm_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(lean_object* v_second_726_, lean_object* v_00___727_){
_start:
{
uint8_t v___x_728_; lean_object* v___x_729_; 
v___x_728_ = 1;
v___x_729_ = l_Std_Time_TimeZone_Offset_toIsoString(v_second_726_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(lean_object* v_second_732_, lean_object* v_identifier_733_, lean_object* v_abbreviation_734_){
_start:
{
uint8_t v___x_735_; uint8_t v___y_737_; uint8_t v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_746_; 
v___x_735_ = 0;
if (lean_obj_tag(v_abbreviation_734_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_box(0);
lean_inc(v_second_732_);
v___x_753_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(v_second_732_, v___x_752_);
v___y_746_ = v___x_753_;
goto v___jp_745_;
}
else
{
lean_object* v_val_754_; 
v_val_754_ = lean_ctor_get(v_abbreviation_734_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v_abbreviation_734_, 1);
v___y_746_ = v_val_754_;
goto v___jp_745_;
}
v___jp_736_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_741_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_741_, 0, v_second_732_);
lean_ctor_set(v___x_741_, 1, v___y_739_);
lean_ctor_set(v___x_741_, 2, v___y_740_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*3, v___x_735_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*3 + 1, v___y_737_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*3 + 2, v___y_738_);
v___x_742_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0));
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_744_, 0, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
lean_ctor_set(v___x_744_, 2, v___x_743_);
return v___x_744_;
}
v___jp_745_:
{
uint8_t v___x_747_; uint8_t v___x_748_; 
v___x_747_ = 1;
v___x_748_ = 0;
if (lean_obj_tag(v_identifier_733_) == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_box(0);
lean_inc(v_second_732_);
v___x_750_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___lam__0(v_second_732_, v___x_749_);
v___y_737_ = v___x_747_;
v___y_738_ = v___x_748_;
v___y_739_ = v___y_746_;
v___y_740_ = v___x_750_;
goto v___jp_736_;
}
else
{
lean_object* v_val_751_; 
v_val_751_ = lean_ctor_get(v_identifier_733_, 0);
lean_inc(v_val_751_);
lean_dec_ref_known(v_identifier_733_, 1);
v___y_737_ = v___x_747_;
v___y_738_ = v___x_748_;
v___y_739_ = v___y_746_;
v___y_740_ = v_val_751_;
goto v___jp_736_;
}
}
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_nat_to_int(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_UTC___closed__2));
v___x_761_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_UTC___closed__0, &l_Std_Time_TimeZone_ZoneRules_UTC___closed__0_once, _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__0);
v___x_762_ = l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone(v___x_761_, v___x_760_, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_UTC(void){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_UTC___closed__3, &l_Std_Time_TimeZone_ZoneRules_UTC___closed__3_once, _init_l_Std_Time_TimeZone_ZoneRules_UTC___closed__3);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(lean_object* v_zr_764_, lean_object* v_timestamp_765_){
_start:
{
lean_object* v_initialLocalTimeType_766_; lean_object* v_transitions_767_; lean_object* v_transitionRule_768_; lean_object* v___x_769_; 
v_initialLocalTimeType_766_ = lean_ctor_get(v_zr_764_, 0);
lean_inc_ref(v_initialLocalTimeType_766_);
v_transitions_767_ = lean_ctor_get(v_zr_764_, 1);
lean_inc_ref(v_transitions_767_);
v_transitionRule_768_ = lean_ctor_get(v_zr_764_, 2);
lean_inc(v_transitionRule_768_);
lean_dec_ref(v_zr_764_);
v___x_769_ = l_Std_Time_TimeZone_Transition_findTransitionIndexForTimestamp(v_transitions_767_, v_timestamp_765_);
if (lean_obj_tag(v___x_769_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_val_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = lean_array_get_size(v_transitions_767_);
v___x_772_ = lean_nat_dec_lt(v_val_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_dec(v_val_770_);
lean_dec(v_transitionRule_768_);
lean_dec_ref(v_transitions_767_);
return v_initialLocalTimeType_766_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
lean_dec_ref(v_initialLocalTimeType_766_);
v___x_773_ = lean_array_fget(v_transitions_767_, v_val_770_);
lean_dec_ref(v_transitions_767_);
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_add(v_val_770_, v___x_774_);
lean_dec(v_val_770_);
v___x_776_ = lean_nat_dec_eq(v___x_775_, v___x_771_);
lean_dec(v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v_localTimeType_777_; 
lean_dec(v_transitionRule_768_);
v_localTimeType_777_ = lean_ctor_get(v___x_773_, 1);
lean_inc_ref(v_localTimeType_777_);
lean_dec(v___x_773_);
return v_localTimeType_777_;
}
else
{
if (lean_obj_tag(v_transitionRule_768_) == 1)
{
lean_object* v_val_778_; lean_object* v_localTimeType_779_; lean_object* v_tz_780_; lean_object* v_offset_781_; lean_object* v_name_782_; lean_object* v_abbreviation_783_; uint8_t v_isDST_784_; uint8_t v_wall_785_; uint8_t v_utLocal_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_val_778_ = lean_ctor_get(v_transitionRule_768_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v_transitionRule_768_, 1);
v_localTimeType_779_ = lean_ctor_get(v___x_773_, 1);
lean_inc_ref(v_localTimeType_779_);
lean_dec(v___x_773_);
v_tz_780_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_val_778_, v_timestamp_765_);
v_offset_781_ = lean_ctor_get(v_tz_780_, 0);
lean_inc(v_offset_781_);
v_name_782_ = lean_ctor_get(v_tz_780_, 1);
lean_inc_ref(v_name_782_);
v_abbreviation_783_ = lean_ctor_get(v_tz_780_, 2);
lean_inc_ref(v_abbreviation_783_);
v_isDST_784_ = lean_ctor_get_uint8(v_tz_780_, sizeof(void*)*3);
lean_dec_ref(v_tz_780_);
v_wall_785_ = lean_ctor_get_uint8(v_localTimeType_779_, sizeof(void*)*3 + 1);
v_utLocal_786_ = lean_ctor_get_uint8(v_localTimeType_779_, sizeof(void*)*3 + 2);
v_isSharedCheck_793_ = !lean_is_exclusive(v_localTimeType_779_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; lean_object* v_unused_795_; lean_object* v_unused_796_; 
v_unused_794_ = lean_ctor_get(v_localTimeType_779_, 2);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_localTimeType_779_, 1);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_localTimeType_779_, 0);
lean_dec(v_unused_796_);
v___x_788_ = v_localTimeType_779_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_dec(v_localTimeType_779_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 2, v_name_782_);
lean_ctor_set(v___x_788_, 1, v_abbreviation_783_);
lean_ctor_set(v___x_788_, 0, v_offset_781_);
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_offset_781_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_abbreviation_783_);
lean_ctor_set(v_reuseFailAlloc_792_, 2, v_name_782_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, sizeof(void*)*3 + 1, v_wall_785_);
lean_ctor_set_uint8(v_reuseFailAlloc_792_, sizeof(void*)*3 + 2, v_utLocal_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_ctor_set_uint8(v___x_791_, sizeof(void*)*3, v_isDST_784_);
return v___x_791_;
}
}
}
else
{
lean_object* v_localTimeType_797_; 
lean_dec(v_transitionRule_768_);
v_localTimeType_797_ = lean_ctor_get(v___x_773_, 1);
lean_inc_ref(v_localTimeType_797_);
lean_dec(v___x_773_);
return v_localTimeType_797_;
}
}
}
}
else
{
lean_dec(v___x_769_);
lean_dec(v_transitionRule_768_);
lean_dec_ref(v_transitions_767_);
return v_initialLocalTimeType_766_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp___boxed(lean_object* v_zr_798_, lean_object* v_timestamp_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_798_, v_timestamp_799_);
lean_dec_ref(v_timestamp_799_);
return v_res_800_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_unsigned_to_nat(1000000000u);
v___x_802_ = lean_nat_to_int(v___x_801_);
return v___x_802_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0(lean_object* v_wallTime_803_, lean_object* v_as_804_, size_t v_sz_805_, size_t v_i_806_, lean_object* v_b_807_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = lean_usize_dec_lt(v_i_806_, v_sz_805_);
if (v___x_808_ == 0)
{
return v_b_807_;
}
else
{
lean_object* v_snd_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_839_; 
v_snd_809_ = lean_ctor_get(v_b_807_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v_b_807_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v_b_807_, 0);
lean_dec(v_unused_840_);
v___x_811_ = v_b_807_;
v_isShared_812_ = v_isSharedCheck_839_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_snd_809_);
lean_dec(v_b_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_839_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_gmtOffset_813_; lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v_second_816_; lean_object* v_nano_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_nanos_821_; lean_object* v___x_822_; lean_object* v_nanos_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_gmtOffset_813_ = lean_ctor_get(v_snd_809_, 0);
v_a_814_ = lean_array_uget_borrowed(v_as_804_, v_i_806_);
lean_inc(v_a_814_);
v___x_815_ = l_Std_Time_TimeZone_Transition_timestamp(v_a_814_);
v_second_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_second_816_);
v_nano_817_ = lean_ctor_get(v___x_815_, 1);
lean_inc(v_nano_817_);
lean_dec_ref(v___x_815_);
v___x_818_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0);
v___x_820_ = lean_int_mul(v_second_816_, v___x_819_);
lean_dec(v_second_816_);
v_nanos_821_ = lean_int_add(v___x_820_, v_nano_817_);
lean_dec(v_nano_817_);
lean_dec(v___x_820_);
v___x_822_ = lean_int_mul(v_gmtOffset_813_, v___x_819_);
v_nanos_823_ = lean_int_add(v___x_822_, v___x_818_);
lean_dec(v___x_822_);
v___x_824_ = lean_int_add(v_nanos_821_, v_nanos_823_);
lean_dec(v_nanos_823_);
lean_dec(v_nanos_821_);
v___x_825_ = l_Std_Time_Duration_ofNanoseconds(v___x_824_);
lean_dec(v___x_824_);
v___x_826_ = l_Std_Time_Duration_instDecidableLt(v_wallTime_803_, v___x_825_);
lean_dec_ref(v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v_localTimeType_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec(v_snd_809_);
v_localTimeType_827_ = lean_ctor_get(v_a_814_, 1);
v___x_828_ = lean_box(0);
lean_inc_ref(v_localTimeType_827_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 1, v_localTimeType_827_);
lean_ctor_set(v___x_811_, 0, v___x_828_);
v___x_830_ = v___x_811_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_localTimeType_827_);
v___x_830_ = v_reuseFailAlloc_834_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
size_t v___x_831_; size_t v___x_832_; 
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_add(v_i_806_, v___x_831_);
v_i_806_ = v___x_832_;
v_b_807_ = v___x_830_;
goto _start;
}
}
else
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_inc(v_snd_809_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v_snd_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_835_);
v___x_837_ = v___x_811_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_snd_809_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_wallTime_803_ = stack[0].m_obj;
lean_object* v_as_804_ = stack[1].m_obj;
size_t v_sz_805_ = stack[2].m_num;
size_t v_i_806_ = stack[3].m_num;
lean_object* v_b_807_ = stack[4].m_obj;
lean_object* v_res_841_;
v_res_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0(v_wallTime_803_, v_as_804_, v_sz_805_, v_i_806_, v_b_807_);
stack->m_obj
 = v_res_841_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___boxed(lean_object* v_wallTime_842_, lean_object* v_as_843_, lean_object* v_sz_844_, lean_object* v_i_845_, lean_object* v_b_846_){
_start:
{
size_t v_sz_boxed_847_; size_t v_i_boxed_848_; lean_object* v_res_849_; 
v_sz_boxed_847_ = lean_unbox_usize(v_sz_844_);
lean_dec(v_sz_844_);
v_i_boxed_848_ = lean_unbox_usize(v_i_845_);
lean_dec(v_i_845_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0(v_wallTime_842_, v_as_843_, v_sz_boxed_847_, v_i_boxed_848_, v_b_846_);
lean_dec_ref(v_as_843_);
lean_dec_ref(v_wallTime_842_);
return v_res_849_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(lean_object* v_wallTime_850_, lean_object* v_as_851_, size_t v_sz_852_, size_t v_i_853_, lean_object* v_b_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
if (v___x_855_ == 0)
{
return v_b_854_;
}
else
{
lean_object* v_snd_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_886_; 
v_snd_856_ = lean_ctor_get(v_b_854_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_b_854_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_b_854_, 0);
lean_dec(v_unused_887_);
v___x_858_ = v_b_854_;
v_isShared_859_ = v_isSharedCheck_886_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snd_856_);
lean_dec(v_b_854_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_886_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_gmtOffset_860_; lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v_second_863_; lean_object* v_nano_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_nanos_868_; lean_object* v___x_869_; lean_object* v_nanos_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_gmtOffset_860_ = lean_ctor_get(v_snd_856_, 0);
v_a_861_ = lean_array_uget_borrowed(v_as_851_, v_i_853_);
lean_inc(v_a_861_);
v___x_862_ = l_Std_Time_TimeZone_Transition_timestamp(v_a_861_);
v_second_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_second_863_);
v_nano_864_ = lean_ctor_get(v___x_862_, 1);
lean_inc(v_nano_864_);
lean_dec_ref(v___x_862_);
v___x_865_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_866_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0);
v___x_867_ = lean_int_mul(v_second_863_, v___x_866_);
lean_dec(v_second_863_);
v_nanos_868_ = lean_int_add(v___x_867_, v_nano_864_);
lean_dec(v_nano_864_);
lean_dec(v___x_867_);
v___x_869_ = lean_int_mul(v_gmtOffset_860_, v___x_866_);
v_nanos_870_ = lean_int_add(v___x_869_, v___x_865_);
lean_dec(v___x_869_);
v___x_871_ = lean_int_add(v_nanos_868_, v_nanos_870_);
lean_dec(v_nanos_870_);
lean_dec(v_nanos_868_);
v___x_872_ = l_Std_Time_Duration_ofNanoseconds(v___x_871_);
lean_dec(v___x_871_);
v___x_873_ = l_Std_Time_Duration_instDecidableLt(v_wallTime_850_, v___x_872_);
lean_dec_ref(v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v_localTimeType_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec(v_snd_856_);
v_localTimeType_874_ = lean_ctor_get(v_a_861_, 1);
v___x_875_ = lean_box(0);
lean_inc_ref(v_localTimeType_874_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_localTimeType_874_);
lean_ctor_set(v___x_858_, 0, v___x_875_);
v___x_877_ = v___x_858_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_localTimeType_874_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
size_t v___x_878_; size_t v___x_879_; lean_object* v___x_880_; 
v___x_878_ = ((size_t)1ULL);
v___x_879_ = lean_usize_add(v_i_853_, v___x_878_);
v___x_880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0(v_wallTime_850_, v_as_851_, v_sz_852_, v___x_879_, v___x_877_);
return v___x_880_;
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_inc(v_snd_856_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v_snd_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_882_);
v___x_884_ = v___x_858_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_snd_856_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_wallTime_850_ = stack[0].m_obj;
lean_object* v_as_851_ = stack[1].m_obj;
size_t v_sz_852_ = stack[2].m_num;
size_t v_i_853_ = stack[3].m_num;
lean_object* v_b_854_ = stack[4].m_obj;
lean_object* v_res_888_;
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_850_, v_as_851_, v_sz_852_, v_i_853_, v_b_854_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0___boxed(lean_object* v_wallTime_889_, lean_object* v_as_890_, lean_object* v_sz_891_, lean_object* v_i_892_, lean_object* v_b_893_){
_start:
{
size_t v_sz_boxed_894_; size_t v_i_boxed_895_; lean_object* v_res_896_; 
v_sz_boxed_894_ = lean_unbox_usize(v_sz_891_);
lean_dec(v_sz_891_);
v_i_boxed_895_ = lean_unbox_usize(v_i_892_);
lean_dec(v_i_892_);
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_889_, v_as_890_, v_sz_boxed_894_, v_i_boxed_895_, v_b_893_);
lean_dec_ref(v_as_890_);
lean_dec_ref(v_wallTime_889_);
return v_res_896_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0, &l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedLocalTimeType_default___closed__0);
v___x_898_ = lean_int_neg(v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object* v_zr_899_, lean_object* v_wallTime_900_){
_start:
{
lean_object* v_initialLocalTimeType_901_; lean_object* v_transitions_902_; lean_object* v_transitionRule_903_; lean_object* v___x_904_; lean_object* v___x_905_; size_t v_sz_906_; size_t v___x_907_; lean_object* v___x_908_; lean_object* v_fst_909_; 
v_initialLocalTimeType_901_ = lean_ctor_get(v_zr_899_, 0);
lean_inc_ref(v_initialLocalTimeType_901_);
v_transitions_902_ = lean_ctor_get(v_zr_899_, 1);
lean_inc_ref(v_transitions_902_);
v_transitionRule_903_ = lean_ctor_get(v_zr_899_, 2);
lean_inc(v_transitionRule_903_);
lean_dec_ref(v_zr_899_);
v___x_904_ = lean_box(0);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_initialLocalTimeType_901_);
v_sz_906_ = lean_array_size(v_transitions_902_);
v___x_907_ = ((size_t)0ULL);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0(v_wallTime_900_, v_transitions_902_, v_sz_906_, v___x_907_, v___x_905_);
lean_dec_ref(v_transitions_902_);
v_fst_909_ = lean_ctor_get(v___x_908_, 0);
if (lean_obj_tag(v_fst_909_) == 0)
{
if (lean_obj_tag(v_transitionRule_903_) == 1)
{
lean_object* v_snd_910_; lean_object* v_val_911_; lean_object* v_gmtOffset_912_; uint8_t v_wall_913_; uint8_t v_utLocal_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_937_; 
v_snd_910_ = lean_ctor_get(v___x_908_, 1);
lean_inc(v_snd_910_);
lean_dec_ref(v___x_908_);
v_val_911_ = lean_ctor_get(v_transitionRule_903_, 0);
lean_inc(v_val_911_);
lean_dec_ref_known(v_transitionRule_903_, 1);
v_gmtOffset_912_ = lean_ctor_get(v_snd_910_, 0);
v_wall_913_ = lean_ctor_get_uint8(v_snd_910_, sizeof(void*)*3 + 1);
v_utLocal_914_ = lean_ctor_get_uint8(v_snd_910_, sizeof(void*)*3 + 2);
v_isSharedCheck_937_ = !lean_is_exclusive(v_snd_910_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; lean_object* v_unused_939_; 
v_unused_938_ = lean_ctor_get(v_snd_910_, 2);
lean_dec(v_unused_938_);
v_unused_939_ = lean_ctor_get(v_snd_910_, 1);
lean_dec(v_unused_939_);
v___x_916_ = v_snd_910_;
v_isShared_917_ = v_isSharedCheck_937_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_gmtOffset_912_);
lean_dec(v_snd_910_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_937_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_second_918_; lean_object* v_nano_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_nanos_924_; lean_object* v___x_925_; lean_object* v_nanos_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_offset_930_; lean_object* v_name_931_; lean_object* v_abbreviation_932_; uint8_t v_isDST_933_; lean_object* v___x_935_; 
v_second_918_ = lean_ctor_get(v_wallTime_900_, 0);
v_nano_919_ = lean_ctor_get(v_wallTime_900_, 1);
v___x_920_ = lean_int_neg(v_gmtOffset_912_);
lean_dec(v_gmtOffset_912_);
v___x_921_ = lean_obj_once(&l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0, &l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0_once, _init_l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___closed__0);
v___x_922_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime_spec__0_spec__0___closed__0);
v___x_923_ = lean_int_mul(v_second_918_, v___x_922_);
v_nanos_924_ = lean_int_add(v___x_923_, v_nano_919_);
lean_dec(v___x_923_);
v___x_925_ = lean_int_mul(v___x_920_, v___x_922_);
lean_dec(v___x_920_);
v_nanos_926_ = lean_int_add(v___x_925_, v___x_921_);
lean_dec(v___x_925_);
v___x_927_ = lean_int_add(v_nanos_924_, v_nanos_926_);
lean_dec(v_nanos_926_);
lean_dec(v_nanos_924_);
v___x_928_ = l_Std_Time_Duration_ofNanoseconds(v___x_927_);
lean_dec(v___x_927_);
v___x_929_ = l_Std_Time_TimeZone_RecurringRule_timezoneAt(v_val_911_, v___x_928_);
lean_dec_ref(v___x_928_);
v_offset_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_offset_930_);
v_name_931_ = lean_ctor_get(v___x_929_, 1);
lean_inc_ref(v_name_931_);
v_abbreviation_932_ = lean_ctor_get(v___x_929_, 2);
lean_inc_ref(v_abbreviation_932_);
v_isDST_933_ = lean_ctor_get_uint8(v___x_929_, sizeof(void*)*3);
lean_dec_ref(v___x_929_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 2, v_name_931_);
lean_ctor_set(v___x_916_, 1, v_abbreviation_932_);
lean_ctor_set(v___x_916_, 0, v_offset_930_);
v___x_935_ = v___x_916_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_offset_930_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_abbreviation_932_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v_name_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3 + 1, v_wall_913_);
lean_ctor_set_uint8(v_reuseFailAlloc_936_, sizeof(void*)*3 + 2, v_utLocal_914_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*3, v_isDST_933_);
return v___x_935_;
}
}
}
else
{
lean_object* v_snd_940_; 
lean_dec(v_transitionRule_903_);
v_snd_940_ = lean_ctor_get(v___x_908_, 1);
lean_inc(v_snd_940_);
lean_dec_ref(v___x_908_);
return v_snd_940_;
}
}
else
{
lean_object* v_val_941_; 
lean_inc_ref(v_fst_909_);
lean_dec_ref(v___x_908_);
lean_dec(v_transitionRule_903_);
v_val_941_ = lean_ctor_get(v_fst_909_, 0);
lean_inc(v_val_941_);
lean_dec_ref_known(v_fst_909_, 1);
return v_val_941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime___boxed(lean_object* v_zr_942_, lean_object* v_wallTime_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_942_, v_wallTime_943_);
lean_dec_ref(v_wallTime_943_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object* v_zr_945_, lean_object* v_tm_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForTimestamp(v_zr_945_, v_tm_946_);
v___x_948_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___x_947_);
lean_dec_ref(v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt___boxed(lean_object* v_zr_949_, lean_object* v_tm_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_zr_949_, v_tm_950_);
lean_dec_ref(v_tm_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone(lean_object* v_tz_952_){
_start:
{
lean_object* v_offset_953_; lean_object* v_name_954_; lean_object* v_abbreviation_955_; uint8_t v_isDST_956_; uint8_t v___x_957_; uint8_t v___x_958_; lean_object* v_ltt_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_offset_953_ = lean_ctor_get(v_tz_952_, 0);
v_name_954_ = lean_ctor_get(v_tz_952_, 1);
v_abbreviation_955_ = lean_ctor_get(v_tz_952_, 2);
v_isDST_956_ = lean_ctor_get_uint8(v_tz_952_, sizeof(void*)*3);
v___x_957_ = 0;
v___x_958_ = 1;
lean_inc_ref(v_name_954_);
lean_inc_ref(v_abbreviation_955_);
lean_inc(v_offset_953_);
v_ltt_959_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_959_, 0, v_offset_953_);
lean_ctor_set(v_ltt_959_, 1, v_abbreviation_955_);
lean_ctor_set(v_ltt_959_, 2, v_name_954_);
lean_ctor_set_uint8(v_ltt_959_, sizeof(void*)*3, v_isDST_956_);
lean_ctor_set_uint8(v_ltt_959_, sizeof(void*)*3 + 1, v___x_957_);
lean_ctor_set_uint8(v_ltt_959_, sizeof(void*)*3 + 2, v___x_958_);
v___x_960_ = ((lean_object*)(l_Std_Time_TimeZone_ZoneRules_fixedOffsetZone___closed__0));
v___x_961_ = lean_box(0);
v___x_962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_962_, 0, v_ltt_959_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
lean_ctor_set(v___x_962_, 2, v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ZoneRules_ofTimeZone___boxed(lean_object* v_tz_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_Time_TimeZone_ZoneRules_ofTimeZone(v_tz_963_);
lean_dec_ref(v_tz_963_);
return v_res_964_;
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
