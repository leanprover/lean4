// Lean compiler output
// Module: Lean.Elab.InfoTree.Types
// Imports: Lean.Data.Position Lean.Data.OpenDecl Lean.MetavarContext Lean.Environment Lean.Data.Json Lean.Server.Rpc.Basic Lean.Widget.Types
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedElabInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__6;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPartialTermInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTermInfo;
static lean_object* l_Lean_Elab_instInhabitedFieldInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfoTree;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__2;
static lean_object* l_Lean_Elab_instInhabitedInfoTree___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedPartialTermInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfoState;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo___closed__1;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__8;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedFieldInfo;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedTacticInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedCommandInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedInfo;
static lean_object* l_Lean_Elab_instInhabitedInfoState___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedElabInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__9;
static size_t l_Lean_Elab_instInhabitedTermInfo___closed__5;
static lean_object* l_Lean_Elab_instInhabitedTacticInfo___closed__2;
static lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1;
static lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__1;
static lean_object* _init_l_Lean_Elab_instInhabitedElabInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedElabInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedElabInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_instInhabitedTermInfo___closed__5() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__4;
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__3;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_instInhabitedTermInfo___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__2;
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedElabInfo___closed__1;
x_3 = l_Lean_Elab_instInhabitedTermInfo___closed__7;
x_4 = l_Lean_Elab_instInhabitedTermInfo___closed__8;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedElabInfo___closed__1;
x_3 = l_Lean_Elab_instInhabitedTermInfo___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPartialTermInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedPartialTermInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedCommandInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedElabInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__7;
x_3 = l_Lean_Elab_instInhabitedTermInfo___closed__8;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedFieldInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__2;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_instInhabitedElabInfo___closed__1;
x_3 = l_Lean_Elab_instInhabitedTacticInfo___closed__1;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedTacticInfo___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTacticInfo___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instInhabitedInfo___closed__1;
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfoTree___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Elab_instInhabitedTermInfo___closed__2;
x_3 = l_Lean_Elab_instInhabitedTermInfo___closed__6;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfoState___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTreeOfMonadLift___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instMonadInfoTreeOfMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTreeOfMonadLift___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_setInfoState___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_setInfoState___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_setInfoState___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_setInfoState___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Data_Position(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MetavarContext(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Rpc_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Position(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Rpc_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedElabInfo___closed__1 = _init_l_Lean_Elab_instInhabitedElabInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedElabInfo___closed__1);
l_Lean_Elab_instInhabitedElabInfo = _init_l_Lean_Elab_instInhabitedElabInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedElabInfo);
l_Lean_Elab_instInhabitedTermInfo___closed__1 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__1);
l_Lean_Elab_instInhabitedTermInfo___closed__2 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__2);
l_Lean_Elab_instInhabitedTermInfo___closed__3 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__3);
l_Lean_Elab_instInhabitedTermInfo___closed__4 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__4();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__4);
l_Lean_Elab_instInhabitedTermInfo___closed__5 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__5();
l_Lean_Elab_instInhabitedTermInfo___closed__6 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__6();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__6);
l_Lean_Elab_instInhabitedTermInfo___closed__7 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__7();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__7);
l_Lean_Elab_instInhabitedTermInfo___closed__8 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__8();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__8);
l_Lean_Elab_instInhabitedTermInfo___closed__9 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__9();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__9);
l_Lean_Elab_instInhabitedTermInfo = _init_l_Lean_Elab_instInhabitedTermInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo);
l_Lean_Elab_instInhabitedPartialTermInfo___closed__1 = _init_l_Lean_Elab_instInhabitedPartialTermInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo___closed__1);
l_Lean_Elab_instInhabitedPartialTermInfo = _init_l_Lean_Elab_instInhabitedPartialTermInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedPartialTermInfo);
l_Lean_Elab_instInhabitedCommandInfo = _init_l_Lean_Elab_instInhabitedCommandInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedCommandInfo);
l_Lean_Elab_instInhabitedFieldInfo___closed__1 = _init_l_Lean_Elab_instInhabitedFieldInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo___closed__1);
l_Lean_Elab_instInhabitedFieldInfo = _init_l_Lean_Elab_instInhabitedFieldInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo);
l_Lean_Elab_instInhabitedTacticInfo___closed__1 = _init_l_Lean_Elab_instInhabitedTacticInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo___closed__1);
l_Lean_Elab_instInhabitedTacticInfo___closed__2 = _init_l_Lean_Elab_instInhabitedTacticInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo___closed__2);
l_Lean_Elab_instInhabitedTacticInfo = _init_l_Lean_Elab_instInhabitedTacticInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo);
l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1 = _init_l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1);
l_Lean_Elab_instInhabitedMacroExpansionInfo = _init_l_Lean_Elab_instInhabitedMacroExpansionInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo);
l_Lean_Elab_instInhabitedInfo___closed__1 = _init_l_Lean_Elab_instInhabitedInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfo___closed__1);
l_Lean_Elab_instInhabitedInfo = _init_l_Lean_Elab_instInhabitedInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfo);
l_Lean_Elab_instInhabitedInfoTree___closed__1 = _init_l_Lean_Elab_instInhabitedInfoTree___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree___closed__1);
l_Lean_Elab_instInhabitedInfoTree = _init_l_Lean_Elab_instInhabitedInfoTree();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree);
l_Lean_Elab_instInhabitedInfoState___closed__1 = _init_l_Lean_Elab_instInhabitedInfoState___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState___closed__1);
l_Lean_Elab_instInhabitedInfoState = _init_l_Lean_Elab_instInhabitedInfoState();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
