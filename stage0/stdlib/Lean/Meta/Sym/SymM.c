// Lean compiler output
// Module: Lean.Meta.Sym.SymM
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.Main
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo_default;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo;
static lean_object* l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0;
static lean_object* l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0;
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedProofInstArgInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedProofInstInfo_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Sym_instInhabitedProofInstInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0;
return x_1;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0 = _init_l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default___closed__0);
l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default = _init_l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo_default);
l_Lean_Meta_Sym_instInhabitedProofInstArgInfo = _init_l_Lean_Meta_Sym_instInhabitedProofInstArgInfo();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedProofInstArgInfo);
l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0 = _init_l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedProofInstInfo_default___closed__0);
l_Lean_Meta_Sym_instInhabitedProofInstInfo_default = _init_l_Lean_Meta_Sym_instInhabitedProofInstInfo_default();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedProofInstInfo_default);
l_Lean_Meta_Sym_instInhabitedProofInstInfo = _init_l_Lean_Meta_Sym_instInhabitedProofInstInfo();
lean_mark_persistent(l_Lean_Meta_Sym_instInhabitedProofInstInfo);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
