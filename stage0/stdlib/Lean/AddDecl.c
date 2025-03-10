// Lean compiler output
// Module: Lean.AddDecl
// Imports: Lean.CoreM Lean.Namespace
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
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_addDecl___lambda__2(lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object*);
lean_object* l_Lean_Environment_addConstAsync(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_addDecl_doAdd___lambda__1___closed__3;
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_addDecl_doAdd___lambda__1___closed__2;
static lean_object* l_Lean_addDecl_doAdd___lambda__3___closed__1;
lean_object* l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__2;
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8(lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_addDecl_doAdd___closed__3;
static lean_object* l_Lean_addDecl___lambda__4___closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___closed__2;
lean_object* lean_io_get_num_heartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_IO_CancelToken_new(lean_object*);
extern lean_object* l_Lean_debug_skipKernelTC;
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl_doAdd___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at_Lean_addDecl_doAdd___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl_doAdd___lambda__1___closed__4;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___closed__1;
static lean_object* l_Lean_addDecl___closed__3;
lean_object* l_Lean_Core_wrapAsyncAsSnapshot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__2___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_addDecl_doAdd___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now(lean_object*);
extern lean_object* l_Task_Priority_default;
lean_object* l_Lean_Declaration_getNames(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler_threshold;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___lambda__4___closed__5;
lean_object* l_Lean_Declaration_getTopLevelNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__1;
lean_object* l_Lean_Environment_AddConstAsyncResult_commitConst(lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__4;
static lean_object* l_Lean_addDecl_doAdd___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2___closed__1;
static lean_object* l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__2;
static lean_object* l_Lean_addDecl_doAdd___lambda__3___closed__3;
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_addDecl_doAdd___closed__1;
static lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl_doAdd___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at_Lean_addDecl_doAdd___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, double, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl_doAdd___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_addDecl___spec__1(lean_object*, lean_object*);
lean_object* lean_add_decl_without_checking(lean_object*, lean_object*);
uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Kernel_Environment_addDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__1;
extern lean_object* l_Lean_trace_profiler;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___closed__4;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Core_logSnapshotTask(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5___closed__1;
static lean_object* l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_addDecl_doAdd___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl_doAdd___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___boxed(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
static lean_object* _init_l_Lean_Kernel_Environment_addDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_debug_skipKernelTC;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Kernel_Environment_addDecl___closed__1;
x_6 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; lean_object* x_9; 
x_7 = l_Lean_Core_getMaxHeartbeats(x_2);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = lean_add_decl(x_1, x_8, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_add_decl_without_checking(x_1, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Kernel_Environment_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_Core_getMaxHeartbeats(x_2);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = l_Lean_Kernel_Environment_addDecl___closed__1;
x_8 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l_Lean_Environment_addDeclCore(x_1, x_6, x_3, x_4, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Environment_addDeclCore(x_1, x_6, x_3, x_4, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Environment_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
x_1 = x_2;
goto _start;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_AddDecl_0__Lean_isNamespaceName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l___private_Lean_AddDecl_0__Lean_isNamespaceName(x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Environment_registerNamespace(x_1, x_3);
x_1 = x_5;
x_2 = x_3;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_get(x_3, x_4);
lean_dec(x_3);
x_6 = 95;
x_7 = lean_uint32_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(x_1, x_2);
return x_8;
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_addDecl_doAdd___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_interruptExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l_Lean_Kernel_Exception_toMessageData(x_1, x_6);
x_8 = l_Lean_throwError___at_Lean_addDecl_doAdd___spec__3(x_7, x_3, x_4, x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 16)
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2___lambda__1(x_1, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at_Lean_addDecl_doAdd___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2(x_5, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
static lean_object* _init_l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5___closed__1;
x_7 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(x_1, x_8, x_2, x_3, x_4);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = 2;
x_11 = l_Lean_log___at_Lean_Core_wrapAsyncAsSnapshot___spec__13(x_1, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_7);
x_10 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Core_wrapAsyncAsSnapshot___spec__4(x_1, x_5, x_2, x_3, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(x_4, x_7, x_8, x_11);
lean_dec(x_7);
return x_12;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, double x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_7 == 0)
{
double x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2___closed__1;
x_15 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set_float(x_15, sizeof(void*)*2, x_14);
lean_ctor_set_float(x_15, sizeof(void*)*2 + 8, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2 + 16, x_2);
x_16 = lean_box(0);
x_17 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__1(x_4, x_5, x_10, x_6, x_15, x_16, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_float(x_18, sizeof(void*)*2, x_8);
lean_ctor_set_float(x_18, sizeof(void*)*2 + 8, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 16, x_2);
x_19 = lean_box(0);
x_20 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__1(x_4, x_5, x_10, x_6, x_18, x_19, x_11, x_12, x_13);
return x_20;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<exception thrown while producing trace node message>", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 5);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_15 = lean_apply_4(x_9, x_5, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_16, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__2;
x_21 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_20, x_11, x_12, x_19);
lean_dec(x_12);
lean_dec(x_5);
return x_21;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_useHeartbeats;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler_threshold;
return x_1;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static double _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Core_wrapAsyncAsSnapshot___spec__3___rarg(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__1;
x_16 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_io_mono_nanos_now(x_14);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_10);
lean_inc(x_9);
x_114 = lean_apply_3(x_7, x_9, x_10, x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_119 = lean_io_mono_nanos_now(x_117);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; double x_125; double x_126; double x_127; double x_128; double x_129; lean_object* x_130; lean_object* x_131; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
x_123 = 0;
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Float_ofScientific(x_112, x_123, x_124);
lean_dec(x_112);
x_126 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5;
x_127 = lean_float_div(x_125, x_126);
x_128 = l_Float_ofScientific(x_121, x_123, x_124);
lean_dec(x_121);
x_129 = lean_float_div(x_128, x_126);
x_130 = lean_box_float(x_127);
x_131 = lean_box_float(x_129);
lean_ctor_set(x_119, 1, x_131);
lean_ctor_set(x_119, 0, x_130);
lean_ctor_set(x_114, 1, x_119);
lean_ctor_set(x_114, 0, x_118);
x_17 = x_114;
x_18 = x_122;
goto block_110;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; double x_136; double x_137; double x_138; double x_139; double x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_132 = lean_ctor_get(x_119, 0);
x_133 = lean_ctor_get(x_119, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_119);
x_134 = 0;
x_135 = lean_unsigned_to_nat(0u);
x_136 = l_Float_ofScientific(x_112, x_134, x_135);
lean_dec(x_112);
x_137 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5;
x_138 = lean_float_div(x_136, x_137);
x_139 = l_Float_ofScientific(x_132, x_134, x_135);
lean_dec(x_132);
x_140 = lean_float_div(x_139, x_137);
x_141 = lean_box_float(x_138);
x_142 = lean_box_float(x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_114, 1, x_143);
lean_ctor_set(x_114, 0, x_118);
x_17 = x_114;
x_18 = x_133;
goto block_110;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; double x_153; double x_154; double x_155; double x_156; double x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_144 = lean_ctor_get(x_114, 0);
x_145 = lean_ctor_get(x_114, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_114);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_144);
x_147 = lean_io_mono_nanos_now(x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = 0;
x_152 = lean_unsigned_to_nat(0u);
x_153 = l_Float_ofScientific(x_112, x_151, x_152);
lean_dec(x_112);
x_154 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5;
x_155 = lean_float_div(x_153, x_154);
x_156 = l_Float_ofScientific(x_148, x_151, x_152);
lean_dec(x_148);
x_157 = lean_float_div(x_156, x_154);
x_158 = lean_box_float(x_155);
x_159 = lean_box_float(x_157);
if (lean_is_scalar(x_150)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_150;
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_146);
lean_ctor_set(x_161, 1, x_160);
x_17 = x_161;
x_18 = x_149;
goto block_110;
}
}
else
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_114);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_114, 0);
x_164 = lean_ctor_get(x_114, 1);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_163);
x_166 = lean_io_mono_nanos_now(x_164);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; double x_172; double x_173; double x_174; double x_175; double x_176; lean_object* x_177; lean_object* x_178; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
x_170 = 0;
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_Float_ofScientific(x_112, x_170, x_171);
lean_dec(x_112);
x_173 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5;
x_174 = lean_float_div(x_172, x_173);
x_175 = l_Float_ofScientific(x_168, x_170, x_171);
lean_dec(x_168);
x_176 = lean_float_div(x_175, x_173);
x_177 = lean_box_float(x_174);
x_178 = lean_box_float(x_176);
lean_ctor_set(x_166, 1, x_178);
lean_ctor_set(x_166, 0, x_177);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_166);
lean_ctor_set(x_114, 0, x_165);
x_17 = x_114;
x_18 = x_169;
goto block_110;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; double x_183; double x_184; double x_185; double x_186; double x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_179 = lean_ctor_get(x_166, 0);
x_180 = lean_ctor_get(x_166, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_166);
x_181 = 0;
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Float_ofScientific(x_112, x_181, x_182);
lean_dec(x_112);
x_184 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5;
x_185 = lean_float_div(x_183, x_184);
x_186 = l_Float_ofScientific(x_179, x_181, x_182);
lean_dec(x_179);
x_187 = lean_float_div(x_186, x_184);
x_188 = lean_box_float(x_185);
x_189 = lean_box_float(x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_190);
lean_ctor_set(x_114, 0, x_165);
x_17 = x_114;
x_18 = x_180;
goto block_110;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; double x_200; double x_201; double x_202; double x_203; double x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_191 = lean_ctor_get(x_114, 0);
x_192 = lean_ctor_get(x_114, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_114);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_191);
x_194 = lean_io_mono_nanos_now(x_192);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_197 = x_194;
} else {
 lean_dec_ref(x_194);
 x_197 = lean_box(0);
}
x_198 = 0;
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Float_ofScientific(x_112, x_198, x_199);
lean_dec(x_112);
x_201 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5;
x_202 = lean_float_div(x_200, x_201);
x_203 = l_Float_ofScientific(x_195, x_198, x_199);
lean_dec(x_195);
x_204 = lean_float_div(x_203, x_201);
x_205 = lean_box_float(x_202);
x_206 = lean_box_float(x_204);
if (lean_is_scalar(x_197)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_197;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_193);
lean_ctor_set(x_208, 1, x_207);
x_17 = x_208;
x_18 = x_196;
goto block_110;
}
}
block_110:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__2;
x_24 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_23);
if (x_24 == 0)
{
if (x_6 == 0)
{
uint8_t x_90; 
x_90 = 0;
x_25 = x_90;
goto block_89;
}
else
{
lean_object* x_91; double x_92; double x_93; lean_object* x_94; 
x_91 = lean_box(0);
x_92 = lean_unbox_float(x_21);
lean_dec(x_21);
x_93 = lean_unbox_float(x_22);
lean_dec(x_22);
x_94 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_92, x_93, x_5, x_91, x_9, x_10, x_18);
return x_94;
}
}
else
{
if (x_6 == 0)
{
double x_95; double x_96; double x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; double x_102; double x_103; double x_104; uint8_t x_105; 
x_95 = lean_unbox_float(x_22);
x_96 = lean_unbox_float(x_21);
x_97 = lean_float_sub(x_95, x_96);
x_98 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__3;
x_99 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_98);
x_100 = 0;
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Float_ofScientific(x_99, x_100, x_101);
lean_dec(x_99);
x_103 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__4;
x_104 = lean_float_div(x_102, x_103);
x_105 = lean_float_decLt(x_104, x_97);
x_25 = x_105;
goto block_89;
}
else
{
lean_object* x_106; double x_107; double x_108; lean_object* x_109; 
x_106 = lean_box(0);
x_107 = lean_unbox_float(x_21);
lean_dec(x_21);
x_108 = lean_unbox_float(x_22);
lean_dec(x_22);
x_109 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_107, x_108, x_5, x_106, x_9, x_10, x_18);
return x_109;
}
}
block_89:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_st_ref_take(x_10, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = l_Lean_PersistentArray_append___rarg(x_13, x_33);
lean_dec(x_33);
lean_ctor_set(x_28, 0, x_34);
x_35 = lean_st_ref_set(x_10, x_27, x_29);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(x_20, x_9, x_10, x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
lean_dec(x_28);
x_48 = l_Lean_PersistentArray_append___rarg(x_13, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint64(x_49, sizeof(void*)*1, x_46);
lean_ctor_set(x_27, 3, x_49);
x_50 = lean_st_ref_set(x_10, x_27, x_29);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(x_20, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
x_63 = lean_ctor_get(x_27, 2);
x_64 = lean_ctor_get(x_27, 4);
x_65 = lean_ctor_get(x_27, 5);
x_66 = lean_ctor_get(x_27, 6);
x_67 = lean_ctor_get(x_27, 7);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_68 = lean_ctor_get_uint64(x_28, sizeof(void*)*1);
x_69 = lean_ctor_get(x_28, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_70 = x_28;
} else {
 lean_dec_ref(x_28);
 x_70 = lean_box(0);
}
x_71 = l_Lean_PersistentArray_append___rarg(x_13, x_69);
lean_dec(x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 1, 8);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set_uint64(x_72, sizeof(void*)*1, x_68);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_62);
lean_ctor_set(x_73, 2, x_63);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_65);
lean_ctor_set(x_73, 6, x_66);
lean_ctor_set(x_73, 7, x_67);
x_74 = lean_st_ref_set(x_10, x_73, x_29);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(x_20, x_9, x_10, x_75);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_20);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; double x_86; double x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = lean_unbox_float(x_21);
lean_dec(x_21);
x_87 = lean_unbox_float(x_22);
lean_dec(x_22);
x_88 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(x_2, x_3, x_4, x_13, x_20, x_24, x_86, x_87, x_5, x_85, x_9, x_10, x_18);
return x_88;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_io_get_num_heartbeats(x_14);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
lean_inc(x_10);
lean_inc(x_9);
x_304 = lean_apply_3(x_7, x_9, x_10, x_303);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = lean_ctor_get(x_304, 1);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_306);
x_309 = lean_io_get_num_heartbeats(x_307);
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; double x_315; double x_316; lean_object* x_317; lean_object* x_318; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = lean_ctor_get(x_309, 1);
x_313 = 0;
x_314 = lean_unsigned_to_nat(0u);
x_315 = l_Float_ofScientific(x_302, x_313, x_314);
lean_dec(x_302);
x_316 = l_Float_ofScientific(x_311, x_313, x_314);
lean_dec(x_311);
x_317 = lean_box_float(x_315);
x_318 = lean_box_float(x_316);
lean_ctor_set(x_309, 1, x_318);
lean_ctor_set(x_309, 0, x_317);
lean_ctor_set(x_304, 1, x_309);
lean_ctor_set(x_304, 0, x_308);
x_209 = x_304;
x_210 = x_312;
goto block_300;
}
else
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; double x_323; double x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_309, 0);
x_320 = lean_ctor_get(x_309, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_309);
x_321 = 0;
x_322 = lean_unsigned_to_nat(0u);
x_323 = l_Float_ofScientific(x_302, x_321, x_322);
lean_dec(x_302);
x_324 = l_Float_ofScientific(x_319, x_321, x_322);
lean_dec(x_319);
x_325 = lean_box_float(x_323);
x_326 = lean_box_float(x_324);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_304, 1, x_327);
lean_ctor_set(x_304, 0, x_308);
x_209 = x_304;
x_210 = x_320;
goto block_300;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; double x_337; double x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_328 = lean_ctor_get(x_304, 0);
x_329 = lean_ctor_get(x_304, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_304);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_328);
x_331 = lean_io_get_num_heartbeats(x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
x_335 = 0;
x_336 = lean_unsigned_to_nat(0u);
x_337 = l_Float_ofScientific(x_302, x_335, x_336);
lean_dec(x_302);
x_338 = l_Float_ofScientific(x_332, x_335, x_336);
lean_dec(x_332);
x_339 = lean_box_float(x_337);
x_340 = lean_box_float(x_338);
if (lean_is_scalar(x_334)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_334;
}
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_330);
lean_ctor_set(x_342, 1, x_341);
x_209 = x_342;
x_210 = x_333;
goto block_300;
}
}
else
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_304);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_344 = lean_ctor_get(x_304, 0);
x_345 = lean_ctor_get(x_304, 1);
x_346 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_346, 0, x_344);
x_347 = lean_io_get_num_heartbeats(x_345);
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; double x_353; double x_354; lean_object* x_355; lean_object* x_356; 
x_349 = lean_ctor_get(x_347, 0);
x_350 = lean_ctor_get(x_347, 1);
x_351 = 0;
x_352 = lean_unsigned_to_nat(0u);
x_353 = l_Float_ofScientific(x_302, x_351, x_352);
lean_dec(x_302);
x_354 = l_Float_ofScientific(x_349, x_351, x_352);
lean_dec(x_349);
x_355 = lean_box_float(x_353);
x_356 = lean_box_float(x_354);
lean_ctor_set(x_347, 1, x_356);
lean_ctor_set(x_347, 0, x_355);
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_347);
lean_ctor_set(x_304, 0, x_346);
x_209 = x_304;
x_210 = x_350;
goto block_300;
}
else
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; double x_361; double x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_357 = lean_ctor_get(x_347, 0);
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_347);
x_359 = 0;
x_360 = lean_unsigned_to_nat(0u);
x_361 = l_Float_ofScientific(x_302, x_359, x_360);
lean_dec(x_302);
x_362 = l_Float_ofScientific(x_357, x_359, x_360);
lean_dec(x_357);
x_363 = lean_box_float(x_361);
x_364 = lean_box_float(x_362);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_365);
lean_ctor_set(x_304, 0, x_346);
x_209 = x_304;
x_210 = x_358;
goto block_300;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; double x_375; double x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_366 = lean_ctor_get(x_304, 0);
x_367 = lean_ctor_get(x_304, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_304);
x_368 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_368, 0, x_366);
x_369 = lean_io_get_num_heartbeats(x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_372 = x_369;
} else {
 lean_dec_ref(x_369);
 x_372 = lean_box(0);
}
x_373 = 0;
x_374 = lean_unsigned_to_nat(0u);
x_375 = l_Float_ofScientific(x_302, x_373, x_374);
lean_dec(x_302);
x_376 = l_Float_ofScientific(x_370, x_373, x_374);
lean_dec(x_370);
x_377 = lean_box_float(x_375);
x_378 = lean_box_float(x_376);
if (lean_is_scalar(x_372)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_372;
}
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_368);
lean_ctor_set(x_380, 1, x_379);
x_209 = x_380;
x_210 = x_371;
goto block_300;
}
}
block_300:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; 
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__2;
x_216 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_215);
if (x_216 == 0)
{
if (x_6 == 0)
{
uint8_t x_282; 
x_282 = 0;
x_217 = x_282;
goto block_281;
}
else
{
lean_object* x_283; double x_284; double x_285; lean_object* x_286; 
x_283 = lean_box(0);
x_284 = lean_unbox_float(x_213);
lean_dec(x_213);
x_285 = lean_unbox_float(x_214);
lean_dec(x_214);
x_286 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_284, x_285, x_5, x_283, x_9, x_10, x_210);
return x_286;
}
}
else
{
if (x_6 == 0)
{
double x_287; double x_288; double x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; double x_294; uint8_t x_295; 
x_287 = lean_unbox_float(x_214);
x_288 = lean_unbox_float(x_213);
x_289 = lean_float_sub(x_287, x_288);
x_290 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__3;
x_291 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_290);
x_292 = 0;
x_293 = lean_unsigned_to_nat(0u);
x_294 = l_Float_ofScientific(x_291, x_292, x_293);
lean_dec(x_291);
x_295 = lean_float_decLt(x_294, x_289);
x_217 = x_295;
goto block_281;
}
else
{
lean_object* x_296; double x_297; double x_298; lean_object* x_299; 
x_296 = lean_box(0);
x_297 = lean_unbox_float(x_213);
lean_dec(x_213);
x_298 = lean_unbox_float(x_214);
lean_dec(x_214);
x_299 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_297, x_298, x_5, x_296, x_9, x_10, x_210);
return x_299;
}
}
block_281:
{
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_218 = lean_st_ref_take(x_10, x_210);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = !lean_is_exclusive(x_219);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_219, 3);
lean_dec(x_223);
x_224 = !lean_is_exclusive(x_220);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_220, 0);
x_226 = l_Lean_PersistentArray_append___rarg(x_13, x_225);
lean_dec(x_225);
lean_ctor_set(x_220, 0, x_226);
x_227 = lean_st_ref_set(x_10, x_219, x_221);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(x_212, x_9, x_10, x_228);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
return x_229;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_229);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
else
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_229);
if (x_234 == 0)
{
return x_229;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_229, 0);
x_236 = lean_ctor_get(x_229, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_229);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint64_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get_uint64(x_220, sizeof(void*)*1);
x_239 = lean_ctor_get(x_220, 0);
lean_inc(x_239);
lean_dec(x_220);
x_240 = l_Lean_PersistentArray_append___rarg(x_13, x_239);
lean_dec(x_239);
x_241 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set_uint64(x_241, sizeof(void*)*1, x_238);
lean_ctor_set(x_219, 3, x_241);
x_242 = lean_st_ref_set(x_10, x_219, x_221);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(x_212, x_9, x_10, x_243);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_244, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_251 = x_244;
} else {
 lean_dec_ref(x_244);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint64_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_253 = lean_ctor_get(x_219, 0);
x_254 = lean_ctor_get(x_219, 1);
x_255 = lean_ctor_get(x_219, 2);
x_256 = lean_ctor_get(x_219, 4);
x_257 = lean_ctor_get(x_219, 5);
x_258 = lean_ctor_get(x_219, 6);
x_259 = lean_ctor_get(x_219, 7);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_219);
x_260 = lean_ctor_get_uint64(x_220, sizeof(void*)*1);
x_261 = lean_ctor_get(x_220, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 x_262 = x_220;
} else {
 lean_dec_ref(x_220);
 x_262 = lean_box(0);
}
x_263 = l_Lean_PersistentArray_append___rarg(x_13, x_261);
lean_dec(x_261);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 1, 8);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set_uint64(x_264, sizeof(void*)*1, x_260);
x_265 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_254);
lean_ctor_set(x_265, 2, x_255);
lean_ctor_set(x_265, 3, x_264);
lean_ctor_set(x_265, 4, x_256);
lean_ctor_set(x_265, 5, x_257);
lean_ctor_set(x_265, 6, x_258);
lean_ctor_set(x_265, 7, x_259);
x_266 = lean_st_ref_set(x_10, x_265, x_221);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(x_212, x_9, x_10, x_267);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_212);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_268, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_275 = x_268;
} else {
 lean_dec_ref(x_268);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
}
else
{
lean_object* x_277; double x_278; double x_279; lean_object* x_280; 
x_277 = lean_box(0);
x_278 = lean_unbox_float(x_213);
lean_dec(x_213);
x_279 = lean_unbox_float(x_214);
lean_dec(x_214);
x_280 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(x_2, x_3, x_4, x_13, x_212, x_216, x_278, x_279, x_5, x_277, x_9, x_10, x_210);
return x_280;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_inc(x_1);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Core_wrapAsyncAsSnapshot___spec__2(x_1, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__2;
x_15 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_apply_3(x_3, x_6, x_7, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_11);
lean_dec(x_11);
x_27 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4(x_9, x_1, x_4, x_5, x_2, x_26, x_3, x_25, x_6, x_7, x_13);
lean_dec(x_9);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_box(0);
x_30 = lean_unbox(x_11);
lean_dec(x_11);
x_31 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4(x_9, x_1, x_4, x_5, x_2, x_30, x_3, x_29, x_6, x_7, x_28);
lean_dec(x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_2(x_3, x_5, x_6);
x_9 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_8, x_4, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8___rarg___boxed), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typechecking declarations ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl_doAdd___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl_doAdd___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Declaration_getTopLevelNames(x_1);
x_7 = lean_box(0);
x_8 = l_List_mapTR_loop___at_Lean_compileDecls_doCompile___spec__1(x_6, x_7);
x_9 = l_Lean_MessageData_ofList(x_8);
x_10 = l_Lean_addDecl_doAdd___lambda__1___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_addDecl_doAdd___lambda__1___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 11);
lean_inc(x_11);
x_12 = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(x_9, x_10, x_1, x_11);
lean_dec(x_11);
lean_dec(x_10);
lean_inc(x_3);
x_13 = l_Lean_ofExceptKernelException___at_Lean_addDecl_doAdd___spec__1(x_12, x_3, x_4, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_14, x_3, x_4, x_15);
lean_dec(x_3);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hasSorry", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addDecl_doAdd___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declaration uses 'sorry'", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl_doAdd___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addDecl_doAdd___lambda__3___closed__2;
x_2 = l_Lean_addDecl_doAdd___lambda__3___closed__4;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 5);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_MessageLog_hasErrors(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = 0;
x_11 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_addDecl_doAdd___lambda__2(x_1, x_12, x_2, x_3, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_addDecl_doAdd___lambda__3___closed__5;
lean_inc(x_2);
x_15 = l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5(x_14, x_2, x_3, x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_addDecl_doAdd___lambda__2(x_1, x_16, x_2, x_3, x_17);
lean_dec(x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_addDecl_doAdd___lambda__2(x_1, x_19, x_2, x_3, x_7);
return x_20;
}
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Kernel", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addDecl_doAdd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addDecl_doAdd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type checking", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_addDecl_doAdd___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_addDecl_doAdd___lambda__3___boxed), 4, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_addDecl_doAdd___closed__2;
x_9 = 1;
x_10 = l_Lean_addDecl_doAdd___lambda__1___closed__3;
x_11 = lean_box(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___boxed), 8, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_10);
x_13 = l_Lean_addDecl_doAdd___closed__3;
x_14 = lean_box(0);
x_15 = l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8___rarg(x_13, x_5, x_12, x_14, x_2, x_3, x_4);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_addDecl_doAdd___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_addDecl_doAdd___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___at_Lean_addDecl_doAdd___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at_Lean_addDecl_doAdd___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExceptKernelException___at_Lean_addDecl_doAdd___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_MonadExcept_ofExcept___at_Lean_addDecl_doAdd___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = lean_unbox_float(x_8);
lean_dec(x_8);
x_17 = lean_unbox_float(x_9);
lean_dec(x_9);
x_18 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2(x_1, x_14, x_3, x_4, x_5, x_6, x_15, x_16, x_17, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; double x_16; double x_17; lean_object* x_18; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox_float(x_7);
lean_dec(x_7);
x_17 = lean_unbox_float(x_8);
lean_dec(x_8);
x_18 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3(x_1, x_14, x_3, x_4, x_5, x_15, x_16, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_profileitM___at_Lean_addDecl_doAdd___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDecl_doAdd___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDecl_doAdd___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl_doAdd___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addDecl_doAdd___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_addDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_1, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_addDecl_doAdd(x_2, x_5, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_6, x_11);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_5, 5);
lean_inc(x_17);
lean_dec(x_5);
x_18 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_3, x_16, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_17);
lean_free_object(x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_io_error_to_string(x_24);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_17);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_io_error_to_string(x_28);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_MessageData_ofFormat(x_31);
lean_ctor_set(x_12, 1, x_32);
lean_ctor_set(x_12, 0, x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_5, 5);
lean_inc(x_37);
lean_dec(x_5);
x_38 = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(x_3, x_36, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_45 = x_38;
} else {
 lean_dec_ref(x_38);
 x_45 = lean_box(0);
}
x_46 = lean_io_error_to_string(x_43);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_48);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_10);
if (x_51 == 0)
{
return x_10;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_10, 0);
x_53 = lean_ctor_get(x_10, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_10);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_addDecl___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_addDecl___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("addDecl", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addDecl___lambda__4___closed__1;
x_2 = l_Lean_addDecl___lambda__4___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addDecl___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addDecl___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl___lambda__4___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_addDecl___lambda__4___closed__3;
x_2 = 1;
x_3 = l_Lean_addDecl___lambda__4___closed__4;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_ref_get(x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_3, 5);
lean_inc(x_15);
x_16 = 0;
x_17 = 1;
x_18 = lean_unbox(x_9);
lean_dec(x_9);
lean_inc(x_14);
x_19 = l_Lean_Environment_addConstAsync(x_14, x_7, x_18, x_16, x_17, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_8);
lean_inc(x_22);
lean_inc(x_20);
x_24 = l_Lean_Environment_AddConstAsyncResult_commitConst(x_20, x_22, x_23, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_free_object(x_10);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
x_27 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_26, x_3, x_4, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_IO_CancelToken_new(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_addDecl___lambda__1___boxed), 7, 3);
lean_closure_set(x_32, 0, x_22);
lean_closure_set(x_32, 1, x_1);
lean_closure_set(x_32, 2, x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_34 = l_Lean_addDecl___lambda__4___closed__5;
lean_inc(x_3);
lean_inc(x_33);
x_35 = l_Lean_Core_wrapAsyncAsSnapshot(x_32, x_33, x_34, x_3, x_4, x_31);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_closure((void*)(l_Lean_addDecl___lambda__3___boxed), 3, 1);
lean_closure_set(x_38, 0, x_36);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_dec(x_14);
x_40 = l_Task_Priority_default;
x_41 = lean_io_map_task(x_38, x_39, x_40, x_16, x_37);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Syntax_getTailPos_x3f(x_15, x_16);
lean_dec(x_15);
x_46 = lean_box(0);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_free_object(x_41);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_33);
lean_ctor_set(x_47, 3, x_43);
x_48 = l_Lean_Core_logSnapshotTask(x_47, x_3, x_4, x_44);
lean_dec(x_3);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_ctor_set(x_41, 1, x_50);
lean_ctor_set(x_41, 0, x_50);
lean_ctor_set(x_45, 0, x_41);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_33);
lean_ctor_set(x_51, 3, x_43);
x_52 = l_Lean_Core_logSnapshotTask(x_51, x_3, x_4, x_44);
lean_dec(x_3);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
lean_inc(x_53);
lean_ctor_set(x_41, 1, x_53);
lean_ctor_set(x_41, 0, x_53);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_41);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_33);
lean_ctor_set(x_55, 3, x_43);
x_56 = l_Lean_Core_logSnapshotTask(x_55, x_3, x_4, x_44);
lean_dec(x_3);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_41);
x_59 = l_Lean_Syntax_getTailPos_x3f(x_15, x_16);
lean_dec(x_15);
x_60 = lean_box(0);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_33);
lean_ctor_set(x_61, 3, x_57);
x_62 = l_Lean_Core_logSnapshotTask(x_61, x_3, x_4, x_58);
lean_dec(x_3);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
lean_inc(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_63);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_33);
lean_ctor_set(x_67, 3, x_57);
x_68 = l_Lean_Core_logSnapshotTask(x_67, x_3, x_4, x_58);
lean_dec(x_3);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_24);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_24, 0);
x_71 = lean_io_error_to_string(x_70);
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_MessageData_ofFormat(x_72);
lean_ctor_set(x_10, 1, x_73);
lean_ctor_set(x_10, 0, x_15);
lean_ctor_set(x_24, 0, x_10);
return x_24;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_24, 0);
x_75 = lean_ctor_get(x_24, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_24);
x_76 = lean_io_error_to_string(x_74);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_Lean_MessageData_ofFormat(x_77);
lean_ctor_set(x_10, 1, x_78);
lean_ctor_set(x_10, 0, x_15);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_19);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_19, 0);
x_82 = lean_io_error_to_string(x_81);
x_83 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_MessageData_ofFormat(x_83);
lean_ctor_set(x_10, 1, x_84);
lean_ctor_set(x_10, 0, x_15);
lean_ctor_set(x_19, 0, x_10);
return x_19;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_19, 0);
x_86 = lean_ctor_get(x_19, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_19);
x_87 = lean_io_error_to_string(x_85);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_MessageData_ofFormat(x_88);
lean_ctor_set(x_10, 1, x_89);
lean_ctor_set(x_10, 0, x_15);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_10);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_10, 0);
x_92 = lean_ctor_get(x_10, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_10);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_3, 5);
lean_inc(x_94);
x_95 = 0;
x_96 = 1;
x_97 = lean_unbox(x_9);
lean_dec(x_9);
lean_inc(x_93);
x_98 = l_Lean_Environment_addConstAsync(x_93, x_7, x_97, x_95, x_96, x_92);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_8);
lean_inc(x_101);
lean_inc(x_99);
x_103 = l_Lean_Environment_AddConstAsyncResult_commitConst(x_99, x_101, x_102, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = l_Lean_setEnv___at_Lean_compileDecls_doCompile___spec__12(x_105, x_3, x_4, x_104);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_IO_CancelToken_new(x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_alloc_closure((void*)(l_Lean_addDecl___lambda__1___boxed), 7, 3);
lean_closure_set(x_111, 0, x_101);
lean_closure_set(x_111, 1, x_1);
lean_closure_set(x_111, 2, x_99);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_109);
x_113 = l_Lean_addDecl___lambda__4___closed__5;
lean_inc(x_3);
lean_inc(x_112);
x_114 = l_Lean_Core_wrapAsyncAsSnapshot(x_111, x_112, x_113, x_3, x_4, x_110);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_addDecl___lambda__3___boxed), 3, 1);
lean_closure_set(x_117, 0, x_115);
x_118 = lean_ctor_get(x_93, 1);
lean_inc(x_118);
lean_dec(x_93);
x_119 = l_Task_Priority_default;
x_120 = lean_io_map_task(x_117, x_118, x_119, x_95, x_116);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = l_Lean_Syntax_getTailPos_x3f(x_94, x_95);
lean_dec(x_94);
x_125 = lean_box(0);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_123);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_126, 2, x_112);
lean_ctor_set(x_126, 3, x_121);
x_127 = l_Lean_Core_logSnapshotTask(x_126, x_3, x_4, x_122);
lean_dec(x_3);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_124, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_129 = x_124;
} else {
 lean_dec_ref(x_124);
 x_129 = lean_box(0);
}
lean_inc(x_128);
if (lean_is_scalar(x_123)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_123;
}
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_128);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(1, 1, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_132, 0, x_125);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_112);
lean_ctor_set(x_132, 3, x_121);
x_133 = l_Lean_Core_logSnapshotTask(x_132, x_3, x_4, x_122);
lean_dec(x_3);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_93);
lean_dec(x_3);
lean_dec(x_1);
x_134 = lean_ctor_get(x_103, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_103, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_136 = x_103;
} else {
 lean_dec_ref(x_103);
 x_136 = lean_box(0);
}
x_137 = lean_io_error_to_string(x_134);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lean_MessageData_ofFormat(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_94);
lean_ctor_set(x_140, 1, x_139);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_135);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_93);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_142 = lean_ctor_get(x_98, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_98, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_144 = x_98;
} else {
 lean_dec_ref(x_98);
 x_144 = lean_box(0);
}
x_145 = lean_io_error_to_string(x_142);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_Lean_MessageData_ofFormat(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_94);
lean_ctor_set(x_148, 1, x_147);
if (lean_is_scalar(x_144)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_144;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_143);
return x_149;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = 2;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_addDecl___lambda__4(x_1, x_13, x_3, x_4, x_5);
lean_dec(x_4);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_addDecl___lambda__4(x_1, x_22, x_3, x_4, x_5);
lean_dec(x_4);
return x_23;
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addDecl___lambda__4(x_1, x_31, x_3, x_4, x_5);
lean_dec(x_4);
return x_32;
}
case 5:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = l_Lean_addDecl_doAdd(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_33, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_45);
x_50 = 0;
x_51 = lean_box(x_50);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 1, x_51);
lean_ctor_set(x_33, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_33);
x_53 = l_Lean_addDecl___lambda__4(x_1, x_52, x_3, x_4, x_5);
lean_dec(x_4);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
lean_dec(x_33);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_54);
x_58 = 0;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_addDecl___lambda__4(x_1, x_61, x_3, x_4, x_5);
lean_dec(x_4);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_dec(x_43);
lean_dec(x_33);
x_63 = l_Lean_addDecl_doAdd(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 0);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
default: 
{
lean_object* x_72; 
x_72 = l_Lean_addDecl_doAdd(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
return x_72;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_72);
if (x_77 == 0)
{
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 0);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
static lean_object* _init_l_Lean_addDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_async;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 4);
lean_dec(x_10);
lean_inc(x_1);
x_11 = l_Lean_Declaration_getNames(x_1);
x_12 = l_List_foldl___at_Lean_addDecl___spec__1(x_9, x_11);
x_13 = l_Lean_addDecl___closed__3;
lean_ctor_set(x_6, 4, x_13);
lean_ctor_set(x_6, 0, x_12);
x_14 = lean_st_ref_set(x_3, x_6, x_7);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = l_Lean_addDecl___closed__4;
x_18 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_addDecl_doAdd(x_1, x_2, x_3, x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_addDecl___lambda__5(x_1, x_28, x_2, x_3, x_15);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_ctor_get(x_6, 2);
x_33 = lean_ctor_get(x_6, 3);
x_34 = lean_ctor_get(x_6, 5);
x_35 = lean_ctor_get(x_6, 6);
x_36 = lean_ctor_get(x_6, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
lean_inc(x_1);
x_37 = l_Lean_Declaration_getNames(x_1);
x_38 = l_List_foldl___at_Lean_addDecl___spec__1(x_30, x_37);
x_39 = l_Lean_addDecl___closed__3;
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_33);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_34);
lean_ctor_set(x_40, 6, x_35);
lean_ctor_set(x_40, 7, x_36);
x_41 = lean_st_ref_set(x_3, x_40, x_7);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = l_Lean_addDecl___closed__4;
x_45 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Lean_addDecl_doAdd(x_1, x_2, x_3, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(0);
x_56 = l_Lean_addDecl___lambda__5(x_1, x_55, x_2, x_3, x_42);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_addDecl___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addDecl___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDecl___lambda__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDecl___lambda__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_addDecl(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 1;
x_8 = l_Lean_compileDecl(x_1, x_7, x_2, x_3, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Namespace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Namespace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Kernel_Environment_addDecl___closed__1 = _init_l_Lean_Kernel_Environment_addDecl___closed__1();
lean_mark_persistent(l_Lean_Kernel_Environment_addDecl___closed__1);
l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__1 = _init_l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__1();
lean_mark_persistent(l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__1);
l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__2 = _init_l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__2();
lean_mark_persistent(l_Lean_throwInterruptException___at_Lean_addDecl_doAdd___spec__4___rarg___closed__2);
l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5___closed__1 = _init_l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5___closed__1();
lean_mark_persistent(l_Lean_logWarning___at_Lean_addDecl_doAdd___spec__5___closed__1);
l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2___closed__1 = _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__2___closed__1();
l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__1 = _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__1);
l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__2 = _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__3___closed__2);
l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__1 = _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__1);
l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__2 = _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__2);
l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__3 = _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__3);
l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__4 = _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__4();
l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5 = _init_l_Lean_withTraceNode___at_Lean_addDecl_doAdd___spec__6___lambda__4___closed__5();
l_Lean_addDecl_doAdd___lambda__1___closed__1 = _init_l_Lean_addDecl_doAdd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__1___closed__1);
l_Lean_addDecl_doAdd___lambda__1___closed__2 = _init_l_Lean_addDecl_doAdd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__1___closed__2);
l_Lean_addDecl_doAdd___lambda__1___closed__3 = _init_l_Lean_addDecl_doAdd___lambda__1___closed__3();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__1___closed__3);
l_Lean_addDecl_doAdd___lambda__1___closed__4 = _init_l_Lean_addDecl_doAdd___lambda__1___closed__4();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__1___closed__4);
l_Lean_addDecl_doAdd___lambda__3___closed__1 = _init_l_Lean_addDecl_doAdd___lambda__3___closed__1();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__3___closed__1);
l_Lean_addDecl_doAdd___lambda__3___closed__2 = _init_l_Lean_addDecl_doAdd___lambda__3___closed__2();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__3___closed__2);
l_Lean_addDecl_doAdd___lambda__3___closed__3 = _init_l_Lean_addDecl_doAdd___lambda__3___closed__3();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__3___closed__3);
l_Lean_addDecl_doAdd___lambda__3___closed__4 = _init_l_Lean_addDecl_doAdd___lambda__3___closed__4();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__3___closed__4);
l_Lean_addDecl_doAdd___lambda__3___closed__5 = _init_l_Lean_addDecl_doAdd___lambda__3___closed__5();
lean_mark_persistent(l_Lean_addDecl_doAdd___lambda__3___closed__5);
l_Lean_addDecl_doAdd___closed__1 = _init_l_Lean_addDecl_doAdd___closed__1();
lean_mark_persistent(l_Lean_addDecl_doAdd___closed__1);
l_Lean_addDecl_doAdd___closed__2 = _init_l_Lean_addDecl_doAdd___closed__2();
lean_mark_persistent(l_Lean_addDecl_doAdd___closed__2);
l_Lean_addDecl_doAdd___closed__3 = _init_l_Lean_addDecl_doAdd___closed__3();
lean_mark_persistent(l_Lean_addDecl_doAdd___closed__3);
l_Lean_addDecl___lambda__4___closed__1 = _init_l_Lean_addDecl___lambda__4___closed__1();
lean_mark_persistent(l_Lean_addDecl___lambda__4___closed__1);
l_Lean_addDecl___lambda__4___closed__2 = _init_l_Lean_addDecl___lambda__4___closed__2();
lean_mark_persistent(l_Lean_addDecl___lambda__4___closed__2);
l_Lean_addDecl___lambda__4___closed__3 = _init_l_Lean_addDecl___lambda__4___closed__3();
lean_mark_persistent(l_Lean_addDecl___lambda__4___closed__3);
l_Lean_addDecl___lambda__4___closed__4 = _init_l_Lean_addDecl___lambda__4___closed__4();
lean_mark_persistent(l_Lean_addDecl___lambda__4___closed__4);
l_Lean_addDecl___lambda__4___closed__5 = _init_l_Lean_addDecl___lambda__4___closed__5();
lean_mark_persistent(l_Lean_addDecl___lambda__4___closed__5);
l_Lean_addDecl___closed__1 = _init_l_Lean_addDecl___closed__1();
lean_mark_persistent(l_Lean_addDecl___closed__1);
l_Lean_addDecl___closed__2 = _init_l_Lean_addDecl___closed__2();
lean_mark_persistent(l_Lean_addDecl___closed__2);
l_Lean_addDecl___closed__3 = _init_l_Lean_addDecl___closed__3();
lean_mark_persistent(l_Lean_addDecl___closed__3);
l_Lean_addDecl___closed__4 = _init_l_Lean_addDecl___closed__4();
lean_mark_persistent(l_Lean_addDecl___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
