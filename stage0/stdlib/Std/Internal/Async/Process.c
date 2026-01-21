// Lean compiler output
// Module: Std.Internal.Async.Process
// Imports: public import Std.Time public import Std.Internal.UV.System public import Std.Data.HashMap
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_totalMemory();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_availableMemory___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Process_instDecidableEqPId(uint64_t, uint64_t);
lean_object* lean_uv_get_constrained_memory();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1;
lean_object* lean_uv_os_getpriority(uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setPriority(uint64_t, uint64_t);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getParentId();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setCwd(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28;
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Std_Internal_IO_Process_instDecidableEqPId_decEq(uint64_t, uint64_t);
static lean_object* l_Std_Internal_IO_Process_instOrdPId___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_constrainedMemory___boxed(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37;
extern lean_object* l_Std_Time_Millisecond_instInhabitedOffset;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Internal_IO_Process_instReprResourceUsageStats_repr_spec__0(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54;
lean_object* lean_uv_os_getpid();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_constrainedMemory();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprPId;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setProcessTitle___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23;
lean_object* lean_uv_get_total_memory();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21;
lean_object* lean_uv_get_process_title();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_totalMemory___boxed(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setCwd___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instDecidableEqPId_decEq___boxed(lean_object*, lean_object*);
lean_object* l_instNatCastInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getCwd___boxed(lean_object*);
lean_object* lean_uv_os_setpriority(uint64_t, uint64_t);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9;
lean_object* lean_uv_chdir(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprPId___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6;
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprPId___lam__0___closed__1;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprPId___lam__0(uint64_t, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getResourceUsage___boxed(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getResourceUsage();
LEAN_EXPORT uint64_t l_Std_Internal_IO_Process_instInhabitedPId;
static lean_object* l_Std_Internal_IO_Process_instReprPId___closed__0;
static lean_object* l_Std_Internal_IO_Process_getResourceUsage___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instOrdPId;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instInhabitedResourceUsageStats;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instOrdPId_ord___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getExecutablePath();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getPriority(uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setPriority___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getProcessTitle();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_availableMemory();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instDecidableEqPId___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getCwd();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getExecutablePath___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getProcessTitle___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getParentId___boxed(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getResourceUsage___lam__0(lean_object*);
lean_object* lean_uv_set_process_title(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getPriority___boxed(lean_object*, lean_object*);
lean_object* lean_uv_exepath();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getId___boxed(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_uv_get_available_memory();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setProcessTitle(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44;
lean_object* l_Std_Internal_UV_System_getrusage___boxed(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15;
lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24;
lean_object* lean_uv_cwd();
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getId();
static lean_object* l_Std_Internal_IO_Process_getResourceUsage___closed__2;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___boxed(lean_object*, lean_object*);
lean_object* l_Functor_mapRev___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_get_free_memory();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getResourceUsage___lam__0___boxed(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__1;
LEAN_EXPORT uint8_t l_Std_Internal_IO_Process_instOrdPId_ord(uint64_t, uint64_t);
static lean_object* l_Std_Internal_IO_Process_getResourceUsage___closed__0;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_freeMemory();
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0;
static lean_object* l_Std_Internal_IO_Process_instReprPId___lam__0___closed__0;
lean_object* lean_uv_os_getppid();
static uint64_t l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__0;
LEAN_EXPORT uint64_t l_Std_Internal_IO_Process_instInhabitedPId_default;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_freeMemory___boxed(lean_object*);
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50;
static lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Internal_IO_Process_instReprResourceUsageStats_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cpuUserTime", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5;
x_2 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cpuSystemTime", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(17u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("peakResidentSetSizeKb", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sharedMemorySizeKb", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(22u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsharedDataSizeKb", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsharedStackSizeKb", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("minorPageFaults", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("majorPageFaults", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("swapOperations", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(18u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("blockInputOps", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("blockOutputOps", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("messagesSent", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("messagesReceived", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(20u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("signalsReceived", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("voluntaryContextSwitches", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("involuntaryContextSwitches", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 8);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 16);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 24);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 32);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 40);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 48);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 56);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 64);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 72);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 80);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 88);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 96);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2 + 104);
x_18 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5;
x_19 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6;
x_20 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7;
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Std_Time_Internal_UnitVal_instRepr___lam__0(x_2, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = 0;
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_18);
x_34 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12;
x_35 = l_Std_Time_Internal_UnitVal_instRepr___lam__0(x_3, x_21);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_24);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_29);
x_41 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14;
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_18);
x_44 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15;
x_45 = lean_uint64_to_nat(x_4);
x_46 = l_Nat_reprFast(x_45);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_24);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_27);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_29);
x_53 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17;
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_18);
x_56 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18;
x_57 = lean_uint64_to_nat(x_5);
x_58 = l_Nat_reprFast(x_57);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_24);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_27);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_29);
x_65 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20;
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_18);
x_68 = lean_uint64_to_nat(x_6);
x_69 = l_Nat_reprFast(x_68);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_24);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_27);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_29);
x_76 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22;
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_18);
x_79 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23;
x_80 = lean_uint64_to_nat(x_7);
x_81 = l_Nat_reprFast(x_80);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_24);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_27);
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_29);
x_88 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25;
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_18);
x_91 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26;
x_92 = lean_uint64_to_nat(x_8);
x_93 = l_Nat_reprFast(x_92);
x_94 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_24);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_27);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_29);
x_100 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28;
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_18);
x_103 = lean_uint64_to_nat(x_9);
x_104 = l_Nat_reprFast(x_103);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_106, 0, x_91);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_24);
x_108 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_27);
x_110 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_29);
x_111 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30;
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_18);
x_114 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31;
x_115 = lean_uint64_to_nat(x_10);
x_116 = l_Nat_reprFast(x_115);
x_117 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_24);
x_120 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_27);
x_122 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_29);
x_123 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33;
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_18);
x_126 = lean_uint64_to_nat(x_11);
x_127 = l_Nat_reprFast(x_126);
x_128 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_129, 0, x_34);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_24);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_27);
x_133 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_29);
x_134 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35;
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_18);
x_137 = lean_uint64_to_nat(x_12);
x_138 = l_Nat_reprFast(x_137);
x_139 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_140, 0, x_114);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_24);
x_142 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_27);
x_144 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_29);
x_145 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37;
x_146 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_18);
x_148 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38;
x_149 = lean_uint64_to_nat(x_13);
x_150 = l_Nat_reprFast(x_149);
x_151 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_24);
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_27);
x_156 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_29);
x_157 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40;
x_158 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_18);
x_160 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41;
x_161 = lean_uint64_to_nat(x_14);
x_162 = l_Nat_reprFast(x_161);
x_163 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_24);
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_159);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_27);
x_168 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_29);
x_169 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43;
x_170 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_18);
x_172 = lean_uint64_to_nat(x_15);
x_173 = l_Nat_reprFast(x_172);
x_174 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_175, 0, x_91);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_24);
x_177 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_177, 0, x_171);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_27);
x_179 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_29);
x_180 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45;
x_181 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_18);
x_183 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46;
x_184 = lean_uint64_to_nat(x_16);
x_185 = l_Nat_reprFast(x_184);
x_186 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_187 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*1, x_24);
x_189 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_189, 0, x_182);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_27);
x_191 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_29);
x_192 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48;
x_193 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_18);
x_195 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49;
x_196 = lean_uint64_to_nat(x_17);
x_197 = l_Nat_reprFast(x_196);
x_198 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_199, 0, x_195);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_24);
x_201 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52;
x_203 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53;
x_204 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
x_205 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54;
x_206 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*1, x_24);
return x_208;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Process_instReprResourceUsageStats_repr(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprResourceUsageStats() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Process_instReprResourceUsageStats___closed__0;
return x_1;
}
}
static uint64_t _init_l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__1() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__0;
x_2 = l_Std_Time_Millisecond_instInhabitedOffset;
x_3 = lean_alloc_ctor(0, 2, 112);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*2, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 8, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 16, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 24, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 32, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 40, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 48, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 56, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 64, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 72, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 80, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 88, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 96, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*2 + 104, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instInhabitedResourceUsageStats() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default;
return x_1;
}
}
static uint64_t _init_l_Std_Internal_IO_Process_instInhabitedPId_default() {
_start:
{
uint64_t x_1; 
x_1 = l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__0;
return x_1;
}
}
static uint64_t _init_l_Std_Internal_IO_Process_instInhabitedPId() {
_start:
{
uint64_t x_1; 
x_1 = l_Std_Internal_IO_Process_instInhabitedPId_default;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Process_instDecidableEqPId_decEq(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instDecidableEqPId_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Process_instDecidableEqPId_decEq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Process_instDecidableEqPId(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instDecidableEqPId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Process_instDecidableEqPId(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IO_Process_instOrdPId_ord(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_uint64_dec_eq(x_1, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instOrdPId_ord___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Std_Internal_IO_Process_instOrdPId_ord(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instOrdPId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Process_instOrdPId_ord___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instOrdPId() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Process_instOrdPId___closed__0;
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprPId___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PId.mk ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprPId___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Process_instReprPId___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprPId___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Std_Internal_IO_Process_instReprPId___lam__0___closed__1;
x_4 = lean_uint64_to_nat(x_1);
x_5 = l_Nat_reprFast(x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_instReprPId___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_IO_Process_instReprPId___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprPId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Process_instReprPId___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_instReprPId() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Process_instReprPId___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getProcessTitle() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_get_process_title();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getProcessTitle___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_getProcessTitle();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setProcessTitle(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_set_process_title(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setProcessTitle___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Process_setProcessTitle(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getId() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_os_getpid();
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_getId();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getParentId() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_os_getppid();
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getParentId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_getParentId();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getCwd() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_cwd();
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getCwd___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_getCwd();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setCwd(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_chdir(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setCwd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Process_setCwd(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getPriority(uint64_t x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_os_getpriority(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getPriority___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_IO_Process_getPriority(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setPriority(uint64_t x_1, uint64_t x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_uv_os_setpriority(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_setPriority___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_Internal_IO_Process_setPriority(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getResourceUsage___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_ctor_get_uint64(x_1, 0);
x_3 = lean_ctor_get_uint64(x_1, 8);
x_4 = lean_ctor_get_uint64(x_1, 16);
x_5 = lean_ctor_get_uint64(x_1, 24);
x_6 = lean_ctor_get_uint64(x_1, 32);
x_7 = lean_ctor_get_uint64(x_1, 40);
x_8 = lean_ctor_get_uint64(x_1, 48);
x_9 = lean_ctor_get_uint64(x_1, 56);
x_10 = lean_ctor_get_uint64(x_1, 64);
x_11 = lean_ctor_get_uint64(x_1, 72);
x_12 = lean_ctor_get_uint64(x_1, 80);
x_13 = lean_ctor_get_uint64(x_1, 88);
x_14 = lean_ctor_get_uint64(x_1, 96);
x_15 = lean_ctor_get_uint64(x_1, 104);
x_16 = lean_ctor_get_uint64(x_1, 112);
x_17 = lean_ctor_get_uint64(x_1, 120);
x_18 = lean_uint64_to_nat(x_2);
x_19 = l_instNatCastInt___lam__0(x_18);
x_20 = lean_uint64_to_nat(x_3);
x_21 = l_instNatCastInt___lam__0(x_20);
x_22 = lean_alloc_ctor(0, 2, 112);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_uint64(x_22, sizeof(void*)*2, x_4);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 8, x_5);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 16, x_6);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 24, x_7);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 32, x_8);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 40, x_9);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 48, x_10);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 56, x_11);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 64, x_12);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 72, x_13);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 80, x_14);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 88, x_15);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 96, x_16);
lean_ctor_set_uint64(x_22, sizeof(void*)*2 + 104, x_17);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getResourceUsage___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_getResourceUsage___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_getResourceUsage___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_getResourceUsage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Process_getResourceUsage___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Process_getResourceUsage___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_UV_System_getrusage___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getResourceUsage() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Std_Internal_IO_Process_getResourceUsage___closed__0;
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Std_Internal_IO_Process_getResourceUsage___closed__1;
x_6 = l_Std_Internal_IO_Process_getResourceUsage___closed__2;
x_7 = l_Functor_mapRev___redArg(x_4, x_6, x_5);
x_8 = lean_apply_1(x_7, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getResourceUsage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_getResourceUsage();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getExecutablePath() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_exepath();
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_getExecutablePath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_getExecutablePath();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_freeMemory() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_get_free_memory();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_freeMemory___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_freeMemory();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_totalMemory() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_get_total_memory();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_totalMemory___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_totalMemory();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_constrainedMemory() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_get_constrained_memory();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_constrainedMemory___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_constrainedMemory();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_availableMemory() {
_start:
{
lean_object* x_2; 
x_2 = lean_uv_get_available_memory();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Process_availableMemory___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_IO_Process_availableMemory();
return x_2;
}
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_System(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_Process(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_System(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__0);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__1);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__2);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__3);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__4);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__5);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__6);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__7);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__8);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__9);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__10);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__11);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__12);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__13);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__14);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__15);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__16);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__17);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__18);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__19);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__20);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__21);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__22);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__23);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__24);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__25);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__26);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__27);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__28);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__29);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__30);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__31);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__32);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__33);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__34);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__35);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__36);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__37);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__38);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__39);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__40);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__41);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__42);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__43);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__44);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__45);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__46);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__47);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__48);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__49);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__50);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__51);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__52);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__53);
l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats_repr___redArg___closed__54);
l_Std_Internal_IO_Process_instReprResourceUsageStats___closed__0 = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats___closed__0);
l_Std_Internal_IO_Process_instReprResourceUsageStats = _init_l_Std_Internal_IO_Process_instReprResourceUsageStats();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprResourceUsageStats);
l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__0 = _init_l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__0();
l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__1 = _init_l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default___closed__1);
l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default = _init_l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default();
lean_mark_persistent(l_Std_Internal_IO_Process_instInhabitedResourceUsageStats_default);
l_Std_Internal_IO_Process_instInhabitedResourceUsageStats = _init_l_Std_Internal_IO_Process_instInhabitedResourceUsageStats();
lean_mark_persistent(l_Std_Internal_IO_Process_instInhabitedResourceUsageStats);
l_Std_Internal_IO_Process_instInhabitedPId_default = _init_l_Std_Internal_IO_Process_instInhabitedPId_default();
l_Std_Internal_IO_Process_instInhabitedPId = _init_l_Std_Internal_IO_Process_instInhabitedPId();
l_Std_Internal_IO_Process_instOrdPId___closed__0 = _init_l_Std_Internal_IO_Process_instOrdPId___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Process_instOrdPId___closed__0);
l_Std_Internal_IO_Process_instOrdPId = _init_l_Std_Internal_IO_Process_instOrdPId();
lean_mark_persistent(l_Std_Internal_IO_Process_instOrdPId);
l_Std_Internal_IO_Process_instReprPId___lam__0___closed__0 = _init_l_Std_Internal_IO_Process_instReprPId___lam__0___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprPId___lam__0___closed__0);
l_Std_Internal_IO_Process_instReprPId___lam__0___closed__1 = _init_l_Std_Internal_IO_Process_instReprPId___lam__0___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprPId___lam__0___closed__1);
l_Std_Internal_IO_Process_instReprPId___closed__0 = _init_l_Std_Internal_IO_Process_instReprPId___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprPId___closed__0);
l_Std_Internal_IO_Process_instReprPId = _init_l_Std_Internal_IO_Process_instReprPId();
lean_mark_persistent(l_Std_Internal_IO_Process_instReprPId);
l_Std_Internal_IO_Process_getResourceUsage___closed__0 = _init_l_Std_Internal_IO_Process_getResourceUsage___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Process_getResourceUsage___closed__0);
l_Std_Internal_IO_Process_getResourceUsage___closed__1 = _init_l_Std_Internal_IO_Process_getResourceUsage___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Process_getResourceUsage___closed__1);
l_Std_Internal_IO_Process_getResourceUsage___closed__2 = _init_l_Std_Internal_IO_Process_getResourceUsage___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Process_getResourceUsage___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
