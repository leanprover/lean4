// Lean compiler output
// Module: Lake.Build.Basic
// Imports: Init Lake.Util.Log Lake.Util.Exit Lake.Util.Lift Lake.Config.Context Lake.Build.Trace
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
static lean_object* l_Lake_getNoBuild___rarg___closed__1;
LEAN_EXPORT uint8_t l_Lake_BuildConfig_trustHash___default;
LEAN_EXPORT lean_object* l_Lake_getIsQuiet(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_OpaqueJob_nonemptyType;
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildConfig_noBuild___default;
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildConfig_outLv___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_getVerbosity___rarg___lambda__1(lean_object*);
static lean_object* l_Lake_getBuildConfig___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrustHash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logStep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getVerbosity___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildConfig_failLv___default;
LEAN_EXPORT uint8_t l_Lake_BuildConfig_oldMode___default;
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildConfig_out___default;
LEAN_EXPORT lean_object* l_Lake_getBuildContext___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoBuild___rarg(lean_object*, lean_object*);
uint8_t l_Lake_Verbosity_minLogLv(uint8_t);
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildConfig_verbosity___default;
LEAN_EXPORT uint8_t l_Lake_BuildConfig_outLv(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildContext(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getVerbosity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getIsOldMode___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getTrustHash___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildConfig_showProgress(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getBuildContext___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getIsVerbose(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildConfig_showProgress___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_getTrustHash___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getIsOldMode(lean_object*);
static lean_object* l_Lake_getVerbosity___rarg___closed__1;
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_getVerbosity___rarg___lambda__1___boxed(lean_object*);
static lean_object* l_Lake_getIsQuiet___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_logStep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_logStep___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getIsVerbose___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lake_getBuildConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getNoBuild___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrustHash___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_getTrustHash___rarg___closed__1;
LEAN_EXPORT uint8_t l_Lake_getNoBuild___rarg___lambda__1(lean_object*);
LEAN_EXPORT uint8_t l_Lake_BuildConfig_ansiMode___default;
LEAN_EXPORT uint8_t l_Lake_getIsOldMode___rarg___lambda__1(lean_object*);
LEAN_EXPORT uint8_t l_Lake_getIsVerbose___rarg___lambda__1(uint8_t);
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_getIsQuiet___rarg___lambda__1(uint8_t);
LEAN_EXPORT lean_object* l_Lake_getNoBuild(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noBuildCode;
LEAN_EXPORT lean_object* l_Lake_getLeanTrace(lean_object*);
static lean_object* l_Lake_getLeanTrace___rarg___closed__1;
static uint32_t _init_l_Lake_noBuildCode() {
_start:
{
uint32_t x_1; 
x_1 = 3;
return x_1;
}
}
static uint8_t _init_l_Lake_BuildConfig_oldMode___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lake_BuildConfig_trustHash___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lake_BuildConfig_noBuild___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lake_BuildConfig_verbosity___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lake_BuildConfig_failLv___default() {
_start:
{
uint8_t x_1; 
x_1 = 3;
return x_1;
}
}
static lean_object* _init_l_Lake_BuildConfig_out___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
static uint8_t _init_l_Lake_BuildConfig_ansiMode___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildConfig_outLv(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_3 = l_Lake_Verbosity_minLogLv(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildConfig_outLv___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_BuildConfig_outLv(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildConfig_showProgress(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_2 == 0)
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_4 = 0;
x_5 = l_Lake_instDecidableEqVerbosity(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_9 = 2;
x_10 = l_Lake_instDecidableEqVerbosity(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = 0;
x_12 = l_Lake_instDecidableEqVerbosity(x_8, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildConfig_showProgress___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_BuildConfig_showProgress(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_OpaqueJob_nonemptyType() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getBuildContext___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildContext___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getBuildContext___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getLeanTrace___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getLeanTrace___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_getLeanTrace___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getLeanTrace___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getLeanTrace___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getLeanTrace___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_getBuildConfig___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getBuildConfig___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_getBuildConfig___rarg___closed__1;
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getBuildConfig___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getBuildConfig___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getBuildConfig___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsOldMode___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
return x_2;
}
}
static lean_object* _init_l_Lake_getIsOldMode___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getIsOldMode___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_getBuildConfig___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
x_6 = l_Lake_getIsOldMode___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getIsOldMode___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsOldMode___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_getIsOldMode___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_getTrustHash___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
return x_2;
}
}
static lean_object* _init_l_Lake_getTrustHash___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getTrustHash___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_getBuildConfig___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
x_6 = l_Lake_getTrustHash___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getTrustHash___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrustHash___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_getTrustHash___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_getNoBuild___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
return x_2;
}
}
static lean_object* _init_l_Lake_getNoBuild___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getNoBuild___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_getBuildConfig___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
x_6 = l_Lake_getNoBuild___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getNoBuild___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getNoBuild___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_getNoBuild___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_getVerbosity___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
return x_2;
}
}
static lean_object* _init_l_Lake_getVerbosity___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getVerbosity___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_getBuildConfig___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
x_6 = l_Lake_getVerbosity___rarg___closed__1;
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getVerbosity___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getVerbosity___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_getVerbosity___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsVerbose___rarg___lambda__1(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 2;
x_3 = l_Lake_instDecidableEqVerbosity(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_getIsVerbose___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getIsVerbose___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_getBuildConfig___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
x_6 = l_Lake_getVerbosity___rarg___closed__1;
lean_inc(x_3);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
x_8 = l_Lake_getIsVerbose___rarg___closed__1;
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getIsVerbose___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsVerbose___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_getIsVerbose___rarg___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_getIsQuiet___rarg___lambda__1(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lake_instDecidableEqVerbosity(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_getIsQuiet___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getIsQuiet___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lake_getBuildConfig___rarg___closed__1;
lean_inc(x_3);
x_5 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_2);
x_6 = l_Lake_getVerbosity___rarg___closed__1;
lean_inc(x_3);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_5);
x_8 = l_Lake_getIsQuiet___rarg___closed__1;
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_getIsQuiet___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getIsQuiet___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_getIsQuiet___rarg___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_logStep___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 0;
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_logStep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_logStep___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_logStep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_logStep(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Lift(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Context(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Lift(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Context(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_noBuildCode = _init_l_Lake_noBuildCode();
l_Lake_BuildConfig_oldMode___default = _init_l_Lake_BuildConfig_oldMode___default();
l_Lake_BuildConfig_trustHash___default = _init_l_Lake_BuildConfig_trustHash___default();
l_Lake_BuildConfig_noBuild___default = _init_l_Lake_BuildConfig_noBuild___default();
l_Lake_BuildConfig_verbosity___default = _init_l_Lake_BuildConfig_verbosity___default();
l_Lake_BuildConfig_failLv___default = _init_l_Lake_BuildConfig_failLv___default();
l_Lake_BuildConfig_out___default = _init_l_Lake_BuildConfig_out___default();
lean_mark_persistent(l_Lake_BuildConfig_out___default);
l_Lake_BuildConfig_ansiMode___default = _init_l_Lake_BuildConfig_ansiMode___default();
l_Lake_OpaqueJob_nonemptyType = _init_l_Lake_OpaqueJob_nonemptyType();
l_Lake_getLeanTrace___rarg___closed__1 = _init_l_Lake_getLeanTrace___rarg___closed__1();
lean_mark_persistent(l_Lake_getLeanTrace___rarg___closed__1);
l_Lake_getBuildConfig___rarg___closed__1 = _init_l_Lake_getBuildConfig___rarg___closed__1();
lean_mark_persistent(l_Lake_getBuildConfig___rarg___closed__1);
l_Lake_getIsOldMode___rarg___closed__1 = _init_l_Lake_getIsOldMode___rarg___closed__1();
lean_mark_persistent(l_Lake_getIsOldMode___rarg___closed__1);
l_Lake_getTrustHash___rarg___closed__1 = _init_l_Lake_getTrustHash___rarg___closed__1();
lean_mark_persistent(l_Lake_getTrustHash___rarg___closed__1);
l_Lake_getNoBuild___rarg___closed__1 = _init_l_Lake_getNoBuild___rarg___closed__1();
lean_mark_persistent(l_Lake_getNoBuild___rarg___closed__1);
l_Lake_getVerbosity___rarg___closed__1 = _init_l_Lake_getVerbosity___rarg___closed__1();
lean_mark_persistent(l_Lake_getVerbosity___rarg___closed__1);
l_Lake_getIsVerbose___rarg___closed__1 = _init_l_Lake_getIsVerbose___rarg___closed__1();
lean_mark_persistent(l_Lake_getIsVerbose___rarg___closed__1);
l_Lake_getIsQuiet___rarg___closed__1 = _init_l_Lake_getIsQuiet___rarg___closed__1();
lean_mark_persistent(l_Lake_getIsQuiet___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
