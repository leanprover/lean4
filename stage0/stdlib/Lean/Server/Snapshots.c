// Lean compiler output
// Module: Lean.Server.Snapshots
// Imports: Init.System.IO Lean.Elab.Import Lean.Elab.Command Lean.Widget.InteractiveDiagnostic
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
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_liftCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5;
extern lean_object* l_Lean_Elab_instInhabitedInfoTree;
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3;
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6;
lean_object* l_outOfBounds___rarg(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_Snapshots_Snapshot_infoTree___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_env(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Snapshots_Snapshot_msgLog(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Server_Snapshots_Snapshot_infoTree___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_instInhabitedInfoTree;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("s.cmdState.infoState.trees.size == 1\n  ", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1;
x_2 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Snapshots", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Snapshots.Snapshot.infoTree", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4;
x_2 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5;
x_3 = lean_unsigned_to_nat(43u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 6);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6;
x_9 = l_panic___at_Lean_Server_Snapshots_Snapshot_infoTree___spec__1(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_5);
lean_dec(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = l_Lean_Elab_instInhabitedInfoTree;
x_13 = l_outOfBounds___rarg(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_instInhabitedInfoTree;
x_15 = l_Lean_PersistentArray_get_x21___rarg(x_14, x_4, x_10);
return x_15;
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = 0;
x_9 = l_Lean_Syntax_getPos_x3f(x_7, x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_st_mk_ref(x_12, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_firstFrontendMacroScope;
x_18 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
x_19 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_10);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_19, 6, x_18);
lean_ctor_set(x_19, 7, x_11);
lean_ctor_set(x_19, 8, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*9, x_8);
lean_inc(x_14);
x_20 = lean_apply_3(x_3, x_19, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_14, x_22);
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
lean_dec(x_9);
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_firstFrontendMacroScope;
x_37 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
x_38 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_32);
lean_ctor_set(x_38, 4, x_10);
lean_ctor_set(x_38, 5, x_36);
lean_ctor_set(x_38, 6, x_37);
lean_ctor_set(x_38, 7, x_11);
lean_ctor_set(x_38, 8, x_11);
lean_ctor_set_uint8(x_38, sizeof(void*)*9, x_8);
lean_inc(x_33);
x_39 = lean_apply_3(x_3, x_38, x_33, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_get(x_33, x_41);
lean_dec(x_33);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_33);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM___rarg___boxed), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_Snapshot_runCoreM___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Snapshots_Snapshot_runCoreM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___rarg___boxed), 4, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Snapshots_Snapshot_runTermElabM___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Snapshots_Snapshot_runTermElabM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Import(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveDiagnostic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__4);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__5);
l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6 = _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6();
lean_mark_persistent(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
