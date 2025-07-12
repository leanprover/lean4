// Lean compiler output
// Module: Lean.Compiler.IR
// Imports: Lean.Compiler.IR.AddExtern Lean.Compiler.IR.Basic Lean.Compiler.IR.Format Lean.Compiler.IR.CompilerM Lean.Compiler.IR.PushProj Lean.Compiler.IR.ElimDeadVars Lean.Compiler.IR.SimpCase Lean.Compiler.IR.ResetReuse Lean.Compiler.IR.NormIds Lean.Compiler.IR.Checker Lean.Compiler.IR.Borrow Lean.Compiler.IR.Boxing Lean.Compiler.IR.RC Lean.Compiler.IR.ExpandResetReuse Lean.Compiler.IR.UnboxResult Lean.Compiler.IR.ElimDeadBranches Lean.Compiler.IR.EmitC Lean.Compiler.IR.Sorry Lean.Compiler.IR.ToIR Lean.Compiler.IR.ToIRType Lean.Compiler.IR.LLVMBindings Lean.Compiler.IR.EmitLLVM
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
static lean_object* l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_594_;
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
static lean_object* l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_594_;
lean_object* l_Lean_IR_elimDeadBranches___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_inferBorrow___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_compile___closed__22;
static lean_object* l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_compile___closed__13;
static lean_object* l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_compile___closed__28;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__24;
static lean_object* l_Lean_IR_compile___closed__17;
static lean_object* l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_5_;
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__2;
static lean_object* l_Lean_IR_compile___closed__21;
lean_object* l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_196__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_;
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
static lean_object* l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_594_;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_compiler_reuse;
static lean_object* l_Lean_IR_compile___closed__27;
static lean_object* l_Lean_IR_compile___closed__31;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR___hyg_594_;
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_594_(lean_object*);
static lean_object* l_Lean_IR_compile___closed__3;
static lean_object* l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_;
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__26;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__4(size_t, size_t, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__10;
static lean_object* l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l_Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_compile___closed__14;
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
static lean_object* l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_5_;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_IR_explicitBoxing___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__0;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__18;
static lean_object* l_Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_compile___closed__30;
static lean_object* l_Lean_IR_compile___closed__20;
static lean_object* l_Lean_IR_compile___closed__5;
static lean_object* l_Lean_IR_compile___closed__19;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_594_;
uint8_t l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__16;
static lean_object* l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l_Lean_IR_compile___closed__23;
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_5_;
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
static lean_object* l_Lean_IR_compile___closed__25;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR___hyg_594_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_594_;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR___hyg_594_;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_IR_explicitRC___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_compile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_594_;
static lean_object* l_Lean_IR_compile___closed__7;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_IR_compile___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_compile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_compile___closed__9;
static lean_object* l_Lean_IR_compile___closed__15;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5_(lean_object*);
lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_IR_compile___closed__4;
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
static lean_object* l_Lean_IR_compile___closed__1;
static lean_object* l_Lean_IR_compile___closed__33;
static lean_object* l_Lean_IR_compile___closed__6;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__32;
static lean_object* l_Lean_IR_compile___closed__29;
static lean_object* _init_l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_5_;
x_2 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("heuristically insert reset/reuse instruction pairs", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_5_;
x_2 = l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_5_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_5_;
x_2 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_;
x_3 = l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_;
x_4 = l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_5_;
x_3 = l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_5_;
x_4 = l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_5_;
x_5 = l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_196__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_pushProj(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_elimDead(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_simpCase(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_normalizeIds(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_expandResetReuse(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_IR_Decl_insertResetReuse(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_IR_compile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__1;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim_dead_branches", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__4;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("push_proj", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__7;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__10;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim_dead", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__13;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_case", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__16;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("borrow", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__18;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__19;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("boxing", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__21;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__22;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rc", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__24;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__25;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_compiler_reuse;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expand_reset_reuse", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__28;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__29;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reset_reuse", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_compile___closed__31;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_compile___closed__32;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_IR_compile___closed__1;
x_6 = l_Lean_IR_compile___closed__2;
lean_inc(x_1);
x_7 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_6, x_5, x_1, x_2, x_3, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_1);
x_9 = l_Lean_IR_checkDecls(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_elimDeadBranches___redArg(x_1, x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_IR_compile___closed__4;
x_15 = l_Lean_IR_compile___closed__5;
lean_inc(x_12);
x_16 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_15, x_14, x_12, x_2, x_3, x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_size(x_12);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__0(x_18, x_19, x_12);
x_21 = l_Lean_IR_compile___closed__7;
x_99 = l_Lean_IR_compile___closed__8;
lean_inc(x_20);
x_100 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_99, x_21, x_20, x_2, x_3, x_17);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_2, 2);
x_103 = l_Lean_IR_compile___closed__27;
x_104 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_102, x_103);
if (x_104 == 0)
{
x_50 = x_20;
x_51 = x_2;
x_52 = x_3;
x_53 = x_101;
goto block_98;
}
else
{
size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_array_size(x_20);
x_106 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__5(x_105, x_19, x_20);
x_107 = l_Lean_IR_compile___closed__32;
x_108 = l_Lean_IR_compile___closed__33;
lean_inc(x_106);
x_109 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_108, x_107, x_106, x_2, x_3, x_101);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_50 = x_106;
x_51 = x_2;
x_52 = x_3;
x_53 = x_110;
goto block_98;
}
block_49:
{
size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_array_size(x_22);
x_27 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__0(x_26, x_19, x_22);
x_28 = l_Lean_IR_compile___closed__8;
lean_inc(x_27);
x_29 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_28, x_21, x_27, x_23, x_24, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_IR_updateSorryDep(x_27, x_23, x_24, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_IR_compile___closed__10;
x_35 = l_Lean_IR_compile___closed__11;
lean_inc(x_32);
x_36 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_35, x_34, x_32, x_23, x_24, x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_32);
x_38 = l_Lean_IR_checkDecls(x_32, x_23, x_24, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_IR_addDecls(x_32, x_23, x_24, x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_32);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_32);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_98:
{
size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_54 = lean_array_size(x_50);
x_55 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__1(x_54, x_19, x_50);
x_56 = l_Lean_IR_compile___closed__13;
x_57 = l_Lean_IR_compile___closed__14;
lean_inc(x_55);
x_58 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_57, x_56, x_55, x_51, x_52, x_53);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_array_size(x_55);
x_61 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__2(x_60, x_19, x_55);
x_62 = l_Lean_IR_compile___closed__16;
x_63 = l_Lean_IR_compile___closed__17;
lean_inc(x_61);
x_64 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_63, x_62, x_61, x_51, x_52, x_59);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_array_size(x_61);
x_67 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__3(x_66, x_19, x_61);
x_68 = l_Lean_IR_inferBorrow___redArg(x_67, x_52, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_IR_compile___closed__19;
x_72 = l_Lean_IR_compile___closed__20;
lean_inc(x_69);
x_73 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_72, x_71, x_69, x_51, x_52, x_70);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_IR_explicitBoxing___redArg(x_69, x_52, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_IR_compile___closed__22;
x_79 = l_Lean_IR_compile___closed__23;
lean_inc(x_76);
x_80 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_79, x_78, x_76, x_51, x_52, x_77);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_IR_explicitRC___redArg(x_76, x_52, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_IR_compile___closed__25;
x_86 = l_Lean_IR_compile___closed__26;
lean_inc(x_83);
x_87 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_86, x_85, x_83, x_51, x_52, x_84);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get(x_51, 2);
x_90 = l_Lean_IR_compile___closed__27;
x_91 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_89, x_90);
if (x_91 == 0)
{
x_22 = x_83;
x_23 = x_51;
x_24 = x_52;
x_25 = x_88;
goto block_49;
}
else
{
size_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_array_size(x_83);
x_93 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__4(x_92, x_19, x_83);
x_94 = l_Lean_IR_compile___closed__29;
x_95 = l_Lean_IR_compile___closed__30;
lean_inc(x_93);
x_96 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_95, x_94, x_93, x_51, x_52, x_88);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_22 = x_93;
x_23 = x_51;
x_24 = x_52;
x_25 = x_97;
goto block_49;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_9);
if (x_111 == 0)
{
return x_9;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_9, 0);
x_113 = lean_ctor_get(x_9, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_9);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_IR_compile_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_compile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_compile(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ir", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_594_;
x_2 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_;
x_2 = l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_594_;
x_2 = l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_594_;
x_2 = l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_;
x_2 = l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR___hyg_594_;
x_2 = l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_;
x_2 = l_Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR___hyg_594_;
x_2 = l_Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(594u);
x_2 = l_Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_compile___closed__0;
x_2 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR___hyg_594_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_compile___closed__9;
x_2 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_594_;
x_3 = l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_594_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_594_;
x_3 = 0;
x_4 = l_Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR___hyg_594_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR___hyg_594_;
x_8 = 1;
x_9 = l_Lean_registerTraceClass(x_7, x_8, x_4, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR___hyg_594_;
x_12 = l_Lean_registerTraceClass(x_11, x_8, x_4, x_10);
return x_12;
}
else
{
return x_9;
}
}
else
{
return x_5;
}
}
}
lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_PushProj(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_SimpCase(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ResetReuse(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Borrow(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_RC(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_UnboxResult(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ElimDeadBranches(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Sorry(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_EmitLLVM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_AddExtern(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_PushProj(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ElimDeadVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_SimpCase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ResetReuse(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Checker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Borrow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Boxing(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_RC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ExpandResetReuse(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_UnboxResult(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ElimDeadBranches(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Sorry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_LLVMBindings(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitLLVM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_);
l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_5_);
l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_5_);
l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_5_);
l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_5_);
l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_5_);
l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_);
l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_);
l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_5_ = _init_l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_5_();
lean_mark_persistent(l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_5_);
if (builtin) {res = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_compiler_reuse = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_compiler_reuse);
lean_dec_ref(res);
}l_Lean_IR_compile___closed__0 = _init_l_Lean_IR_compile___closed__0();
lean_mark_persistent(l_Lean_IR_compile___closed__0);
l_Lean_IR_compile___closed__1 = _init_l_Lean_IR_compile___closed__1();
lean_mark_persistent(l_Lean_IR_compile___closed__1);
l_Lean_IR_compile___closed__2 = _init_l_Lean_IR_compile___closed__2();
lean_mark_persistent(l_Lean_IR_compile___closed__2);
l_Lean_IR_compile___closed__3 = _init_l_Lean_IR_compile___closed__3();
lean_mark_persistent(l_Lean_IR_compile___closed__3);
l_Lean_IR_compile___closed__4 = _init_l_Lean_IR_compile___closed__4();
lean_mark_persistent(l_Lean_IR_compile___closed__4);
l_Lean_IR_compile___closed__5 = _init_l_Lean_IR_compile___closed__5();
lean_mark_persistent(l_Lean_IR_compile___closed__5);
l_Lean_IR_compile___closed__6 = _init_l_Lean_IR_compile___closed__6();
lean_mark_persistent(l_Lean_IR_compile___closed__6);
l_Lean_IR_compile___closed__7 = _init_l_Lean_IR_compile___closed__7();
lean_mark_persistent(l_Lean_IR_compile___closed__7);
l_Lean_IR_compile___closed__8 = _init_l_Lean_IR_compile___closed__8();
lean_mark_persistent(l_Lean_IR_compile___closed__8);
l_Lean_IR_compile___closed__9 = _init_l_Lean_IR_compile___closed__9();
lean_mark_persistent(l_Lean_IR_compile___closed__9);
l_Lean_IR_compile___closed__10 = _init_l_Lean_IR_compile___closed__10();
lean_mark_persistent(l_Lean_IR_compile___closed__10);
l_Lean_IR_compile___closed__11 = _init_l_Lean_IR_compile___closed__11();
lean_mark_persistent(l_Lean_IR_compile___closed__11);
l_Lean_IR_compile___closed__12 = _init_l_Lean_IR_compile___closed__12();
lean_mark_persistent(l_Lean_IR_compile___closed__12);
l_Lean_IR_compile___closed__13 = _init_l_Lean_IR_compile___closed__13();
lean_mark_persistent(l_Lean_IR_compile___closed__13);
l_Lean_IR_compile___closed__14 = _init_l_Lean_IR_compile___closed__14();
lean_mark_persistent(l_Lean_IR_compile___closed__14);
l_Lean_IR_compile___closed__15 = _init_l_Lean_IR_compile___closed__15();
lean_mark_persistent(l_Lean_IR_compile___closed__15);
l_Lean_IR_compile___closed__16 = _init_l_Lean_IR_compile___closed__16();
lean_mark_persistent(l_Lean_IR_compile___closed__16);
l_Lean_IR_compile___closed__17 = _init_l_Lean_IR_compile___closed__17();
lean_mark_persistent(l_Lean_IR_compile___closed__17);
l_Lean_IR_compile___closed__18 = _init_l_Lean_IR_compile___closed__18();
lean_mark_persistent(l_Lean_IR_compile___closed__18);
l_Lean_IR_compile___closed__19 = _init_l_Lean_IR_compile___closed__19();
lean_mark_persistent(l_Lean_IR_compile___closed__19);
l_Lean_IR_compile___closed__20 = _init_l_Lean_IR_compile___closed__20();
lean_mark_persistent(l_Lean_IR_compile___closed__20);
l_Lean_IR_compile___closed__21 = _init_l_Lean_IR_compile___closed__21();
lean_mark_persistent(l_Lean_IR_compile___closed__21);
l_Lean_IR_compile___closed__22 = _init_l_Lean_IR_compile___closed__22();
lean_mark_persistent(l_Lean_IR_compile___closed__22);
l_Lean_IR_compile___closed__23 = _init_l_Lean_IR_compile___closed__23();
lean_mark_persistent(l_Lean_IR_compile___closed__23);
l_Lean_IR_compile___closed__24 = _init_l_Lean_IR_compile___closed__24();
lean_mark_persistent(l_Lean_IR_compile___closed__24);
l_Lean_IR_compile___closed__25 = _init_l_Lean_IR_compile___closed__25();
lean_mark_persistent(l_Lean_IR_compile___closed__25);
l_Lean_IR_compile___closed__26 = _init_l_Lean_IR_compile___closed__26();
lean_mark_persistent(l_Lean_IR_compile___closed__26);
l_Lean_IR_compile___closed__27 = _init_l_Lean_IR_compile___closed__27();
lean_mark_persistent(l_Lean_IR_compile___closed__27);
l_Lean_IR_compile___closed__28 = _init_l_Lean_IR_compile___closed__28();
lean_mark_persistent(l_Lean_IR_compile___closed__28);
l_Lean_IR_compile___closed__29 = _init_l_Lean_IR_compile___closed__29();
lean_mark_persistent(l_Lean_IR_compile___closed__29);
l_Lean_IR_compile___closed__30 = _init_l_Lean_IR_compile___closed__30();
lean_mark_persistent(l_Lean_IR_compile___closed__30);
l_Lean_IR_compile___closed__31 = _init_l_Lean_IR_compile___closed__31();
lean_mark_persistent(l_Lean_IR_compile___closed__31);
l_Lean_IR_compile___closed__32 = _init_l_Lean_IR_compile___closed__32();
lean_mark_persistent(l_Lean_IR_compile___closed__32);
l_Lean_IR_compile___closed__33 = _init_l_Lean_IR_compile___closed__33();
lean_mark_persistent(l_Lean_IR_compile___closed__33);
l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__9____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__10____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__11____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__12____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__13____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__14____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__15____x40_Lean_Compiler_IR___hyg_594_);
l_Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR___hyg_594_ = _init_l_Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR___hyg_594_();
lean_mark_persistent(l_Lean_IR_initFn___closed__16____x40_Lean_Compiler_IR___hyg_594_);
if (builtin) {res = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_594_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
