// Lean compiler output
// Module: Std.Time.DateTime
// Imports: Std.Time.DateTime.Timestamp Std.Time.DateTime.PlainDateTime
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
static lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___closed__1;
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__14;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration(lean_object*, lean_object*);
static lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__15;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateTimeAssumingUTC(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__11;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__16;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
extern lean_object* l_Std_Time_PlainTime_midnight;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__13;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__18;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__2;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__10;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__12;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__3;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__9;
static lean_object* l_Std_Time_PlainDate_instHSubDuration___closed__1;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_getTimeAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__7;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC___boxed(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__6;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainDate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC___boxed(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__8;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__17;
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__4;
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1;
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__19;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateAssumingUTC(lean_object*);
static lean_object* l_Std_Time_PlainDateTime_ofPlainTime___closed__5;
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
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Timestamp_toPlainDateTimeAssumingUTC(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(86400u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2() {
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
x_3 = l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1;
x_4 = lean_int_mul(x_2, x_3);
lean_dec(x_2);
x_5 = l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2;
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
x_3 = l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1;
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
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__1() {
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
x_3 = l_Std_Time_Timestamp_getTimeAssumingUTC___closed__1;
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_int_add(x_4, x_5);
lean_dec(x_4);
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
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toTimestampAssumingUTC(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_3 = l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1;
x_4 = lean_int_mul(x_2, x_3);
lean_dec(x_2);
x_5 = l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Time_PlainDate_instHSubDuration___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instHSubDuration(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_1);
x_4 = l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1;
x_5 = lean_int_mul(x_3, x_4);
lean_dec(x_3);
x_6 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_2);
x_7 = lean_int_mul(x_6, x_4);
lean_dec(x_6);
x_8 = lean_int_neg(x_7);
lean_dec(x_7);
x_9 = l_Std_Time_Timestamp_getTimeAssumingUTC___closed__1;
x_10 = lean_int_mul(x_5, x_9);
lean_dec(x_5);
x_11 = l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2;
x_12 = lean_int_add(x_10, x_11);
lean_dec(x_10);
x_13 = lean_int_mul(x_8, x_9);
lean_dec(x_8);
x_14 = l_Std_Time_PlainDate_instHSubDuration___closed__1;
x_15 = lean_int_add(x_13, x_14);
lean_dec(x_13);
x_16 = lean_int_add(x_12, x_15);
lean_dec(x_15);
lean_dec(x_12);
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
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainDate___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_toPlainDate(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__2;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__3;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__4;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_2 = lean_int_sub(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__6;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__5;
x_3 = lean_int_emod(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__7;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__5;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__8;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__5;
x_3 = lean_int_emod(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__9;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__11;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__12;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_3 = lean_int_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__13;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__6;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__14;
x_3 = lean_int_emod(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__15;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__14;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__16;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__14;
x_3 = lean_int_emod(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__17;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Time_PlainDateTime_ofPlainTime___closed__1;
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__10;
x_3 = l_Std_Time_PlainDateTime_ofPlainTime___closed__18;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_ofPlainTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Time_PlainDateTime_ofPlainTime___closed__19;
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
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toPlainTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_PlainDateTime_toPlainTime(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instHSubDuration(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_4 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_int_neg(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_int_neg(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = l_Std_Time_Timestamp_getTimeAssumingUTC___closed__1;
x_11 = lean_int_mul(x_9, x_10);
lean_dec(x_9);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_int_add(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_14 = lean_int_mul(x_6, x_10);
lean_dec(x_6);
x_15 = lean_int_add(x_14, x_8);
lean_dec(x_8);
lean_dec(x_14);
x_16 = lean_int_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
return x_17;
}
}
lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime_Timestamp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1 = _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1();
lean_mark_persistent(l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__1);
l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2 = _init_l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2();
lean_mark_persistent(l_Std_Time_Timestamp_ofPlainDateAssumingUTC___closed__2);
l_Std_Time_Timestamp_getTimeAssumingUTC___closed__1 = _init_l_Std_Time_Timestamp_getTimeAssumingUTC___closed__1();
lean_mark_persistent(l_Std_Time_Timestamp_getTimeAssumingUTC___closed__1);
l_Std_Time_PlainDate_instHSubDuration___closed__1 = _init_l_Std_Time_PlainDate_instHSubDuration___closed__1();
lean_mark_persistent(l_Std_Time_PlainDate_instHSubDuration___closed__1);
l_Std_Time_PlainDateTime_ofPlainTime___closed__1 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__1();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__1);
l_Std_Time_PlainDateTime_ofPlainTime___closed__2 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__2();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__2);
l_Std_Time_PlainDateTime_ofPlainTime___closed__3 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__3();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__3);
l_Std_Time_PlainDateTime_ofPlainTime___closed__4 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__4();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__4);
l_Std_Time_PlainDateTime_ofPlainTime___closed__5 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__5();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__5);
l_Std_Time_PlainDateTime_ofPlainTime___closed__6 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__6();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__6);
l_Std_Time_PlainDateTime_ofPlainTime___closed__7 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__7();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__7);
l_Std_Time_PlainDateTime_ofPlainTime___closed__8 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__8();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__8);
l_Std_Time_PlainDateTime_ofPlainTime___closed__9 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__9();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__9);
l_Std_Time_PlainDateTime_ofPlainTime___closed__10 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__10();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__10);
l_Std_Time_PlainDateTime_ofPlainTime___closed__11 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__11();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__11);
l_Std_Time_PlainDateTime_ofPlainTime___closed__12 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__12();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__12);
l_Std_Time_PlainDateTime_ofPlainTime___closed__13 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__13();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__13);
l_Std_Time_PlainDateTime_ofPlainTime___closed__14 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__14();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__14);
l_Std_Time_PlainDateTime_ofPlainTime___closed__15 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__15();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__15);
l_Std_Time_PlainDateTime_ofPlainTime___closed__16 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__16();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__16);
l_Std_Time_PlainDateTime_ofPlainTime___closed__17 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__17();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__17);
l_Std_Time_PlainDateTime_ofPlainTime___closed__18 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__18();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__18);
l_Std_Time_PlainDateTime_ofPlainTime___closed__19 = _init_l_Std_Time_PlainDateTime_ofPlainTime___closed__19();
lean_mark_persistent(l_Std_Time_PlainDateTime_ofPlainTime___closed__19);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
