// Lean compiler output
// Module: Lean.Server.Snapshots
// Imports: public import Lean.Elab.Import public import Lean.Elab.Command public import Lean.Widget.InteractiveDiagnostic
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
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3;
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Snapshots_Snapshot_infoTree_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_endPos(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_env(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Snapshots_Snapshot_infoTree_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_instInhabitedInfoTree_default;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Snapshots", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Snapshots.Snapshot.infoTree", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: infoState.trees.size == 1\n  ", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(48u);
x_4 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1;
x_5 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_ctor_get(x_2, 8);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = l_Lean_Elab_InfoState_substituteLazy(x_3);
x_5 = lean_task_get_own(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_6);
x_10 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3;
x_11 = l_panic___at___00Lean_Server_Snapshots_Snapshot_infoTree_spec__0(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Elab_instInhabitedInfoTree_default;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_7);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_6);
x_15 = l_outOfBounds___redArg(x_12);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_PersistentArray_get_x21___redArg(x_12, x_6, x_13);
return x_16;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Parser_isTerminalCommand(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_Snapshots_Snapshot_isAtEnd(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_25; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_25 = l_Lean_Syntax_getPos_x3f(x_7, x_10);
lean_dec(x_7);
if (lean_obj_tag(x_25) == 0)
{
x_11 = x_9;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_11 = x_26;
goto block_24;
}
block_24:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_st_mk_ref(x_8);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = l_Lean_firstFrontendMacroScope;
x_16 = lean_box(0);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_17 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_6);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_11);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_14);
lean_ctor_set(x_17, 6, x_15);
lean_ctor_set(x_17, 7, x_16);
lean_ctor_set(x_17, 8, x_14);
lean_ctor_set(x_17, 9, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*10, x_10);
lean_inc(x_12);
x_18 = lean_apply_3(x_3, x_17, x_12, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_st_ref_get(x_12);
lean_dec(x_12);
lean_dec(x_20);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_st_ref_get(x_12);
lean_dec(x_12);
lean_dec(x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
}
else
{
lean_dec(x_12);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM___boxed), 5, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Snapshots_Snapshot_runCoreM(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_3);
x_6 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Snapshots_Snapshot_runTermElabM(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
lean_object* initialize_Lean_Elab_Import(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveDiagnostic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
