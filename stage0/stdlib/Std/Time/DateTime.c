// Lean compiler output
// Module: Std.Time.DateTime
// Imports: public import Std.Time.DateTime.Timestamp public import Std.Time.DateTime.PlainDateTime import all Std.Time.Date.Unit.Month
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
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateTimeAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0;
static lean_once_cell_t l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1;
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0;
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampAssumingUTC(lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0;
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_instHSubDuration___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instHSubDuration = (const lean_object*)&l_Std_Time_PlainDate_instHSubDuration___closed__0_value;
extern lean_object* l_Std_Time_PlainTime_midnight;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__0;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__2;
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__3;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__4;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__5;
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__6;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__7;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__8;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__9;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__10;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__11;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__12;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__13;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__14;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__15;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__16;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__17;
static lean_once_cell_t l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__18;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_instHSubDuration___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instHSubDuration = (const lean_object*)&l_Std_Time_PlainDateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateTimeAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(86400u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_3 = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0);
x_4 = lean_int_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0);
x_4 = lean_int_ediv(x_2, x_3);
x_5 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Timestamp_toPlainDateAssumingUTC(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_obj_once(&l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0, &l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0);
x_5 = lean_int_mul(x_2, x_4);
x_6 = lean_int_add(x_5, x_3);
lean_dec(x_5);
x_7 = l_Std_Time_PlainTime_ofNanoseconds(x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Timestamp_getTimeAssumingUTC(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_3 = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0);
x_4 = lean_int_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_4 = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__0);
x_5 = lean_int_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_obj_once(&l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1, &l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1_once, _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
x_7 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_2);
x_8 = lean_int_mul(x_7, x_4);
lean_dec(x_7);
x_9 = lean_int_neg(x_8);
lean_dec(x_8);
x_10 = lean_obj_once(&l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0, &l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_instHSubDuration___lam__0___closed__0);
x_11 = lean_obj_once(&l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0, &l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0);
x_12 = lean_int_mul(x_5, x_11);
lean_dec(x_5);
x_13 = lean_int_add(x_12, x_6);
lean_dec(x_12);
x_14 = lean_int_mul(x_9, x_11);
lean_dec(x_9);
x_15 = lean_int_add(x_14, x_10);
lean_dec(x_14);
x_16 = lean_int_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Time_PlainTime_midnight;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_toPlainDate(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__1, &l_Std_Time_PlainDateTime_ofPlainTime___closed__1_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_3 = lean_int_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__2, &l_Std_Time_PlainDateTime_ofPlainTime___closed__2_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2);
x_3 = lean_int_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__3, &l_Std_Time_PlainDateTime_ofPlainTime___closed__3_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3);
x_3 = lean_int_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_2 = lean_int_sub(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__5, &l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5);
x_3 = lean_int_emod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__6, &l_Std_Time_PlainDateTime_ofPlainTime___closed__6_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6);
x_3 = lean_int_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__4, &l_Std_Time_PlainDateTime_ofPlainTime___closed__4_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__7, &l_Std_Time_PlainDateTime_ofPlainTime___closed__7_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7);
x_3 = lean_int_emod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__8, &l_Std_Time_PlainDateTime_ofPlainTime___closed__8_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8);
x_3 = lean_int_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__10, &l_Std_Time_PlainDateTime_ofPlainTime___closed__10_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_3 = lean_int_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__11, &l_Std_Time_PlainDateTime_ofPlainTime___closed__11_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11);
x_3 = lean_int_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__12, &l_Std_Time_PlainDateTime_ofPlainTime___closed__12_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12);
x_3 = lean_int_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__5, &l_Std_Time_PlainDateTime_ofPlainTime___closed__5_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5);
x_3 = lean_int_emod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__14, &l_Std_Time_PlainDateTime_ofPlainTime___closed__14_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14);
x_3 = lean_int_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__13, &l_Std_Time_PlainDateTime_ofPlainTime___closed__13_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__15, &l_Std_Time_PlainDateTime_ofPlainTime___closed__15_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15);
x_3 = lean_int_emod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__16, &l_Std_Time_PlainDateTime_ofPlainTime___closed__16_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16);
x_3 = lean_int_add(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__17, &l_Std_Time_PlainDateTime_ofPlainTime___closed__17_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17);
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__9, &l_Std_Time_PlainDateTime_ofPlainTime___closed__9_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9);
x_3 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__0, &l_Std_Time_PlainDateTime_ofPlainTime___closed__0_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_PlainDateTime_ofPlainTime___closed__18, &l_Std_Time_PlainDateTime_ofPlainTime___closed__18_once, _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_toPlainTime(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_int_neg(x_4);
lean_dec(x_4);
x_10 = lean_int_neg(x_5);
lean_dec(x_5);
x_11 = lean_obj_once(&l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0, &l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0_once, _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__0);
x_12 = lean_int_mul(x_7, x_11);
lean_dec(x_7);
x_13 = lean_int_add(x_12, x_8);
lean_dec(x_8);
lean_dec(x_12);
x_14 = lean_int_mul(x_9, x_11);
lean_dec(x_9);
x_15 = lean_int_add(x_14, x_10);
lean_dec(x_10);
lean_dec(x_14);
x_16 = lean_int_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
return x_17;
}
}
lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
