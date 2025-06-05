// Lean compiler output
// Module: Lean.Compiler.IR
// Imports: Lean.Compiler.IR.Basic Lean.Compiler.IR.Format Lean.Compiler.IR.CompilerM Lean.Compiler.IR.PushProj Lean.Compiler.IR.ElimDeadVars Lean.Compiler.IR.SimpCase Lean.Compiler.IR.ResetReuse Lean.Compiler.IR.NormIds Lean.Compiler.IR.Checker Lean.Compiler.IR.Borrow Lean.Compiler.IR.Boxing Lean.Compiler.IR.RC Lean.Compiler.IR.ExpandResetReuse Lean.Compiler.IR.UnboxResult Lean.Compiler.IR.ElimDeadBranches Lean.Compiler.IR.EmitC Lean.Compiler.IR.CtorLayout Lean.Compiler.IR.Sorry Lean.Compiler.IR.ToIR Lean.Compiler.IR.LLVMBindings Lean.Compiler.IR.EmitLLVM
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
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__8;
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__5;
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__7;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__11;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__3;
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__3;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__12;
uint8_t l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11;
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5;
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__14;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__18;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_compiler_reuse;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_IR_elimDeadBranches(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__1;
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__6;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2;
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__4;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__17;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__10;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__2;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__8;
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3(size_t, size_t, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_185____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__1;
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__16;
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__13;
LEAN_EXPORT lean_object* lean_ir_add_boxed_version(lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitRC(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__9;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__3;
static lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_addBoxedVersionAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4;
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5_(lean_object*);
lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__19;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__7;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_compile___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__1;
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("heuristically insert reset/reuse instruction pairs", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__4;
x_3 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__7;
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__8;
x_3 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__1;
x_4 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__3;
x_3 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__6;
x_4 = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__9;
x_5 = l_Lean_Option_register___at_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_185____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
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
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__2;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_size(x_4);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(x_8, x_1, x_4);
lean_inc(x_9);
x_10 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_2, x_3, x_9, x_6, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_updateSorryDep(x_9, x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__3;
x_16 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__2;
lean_inc(x_13);
x_17 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_15, x_16, x_13, x_6, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_13);
x_19 = l_Lean_IR_checkDecls(x_13, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_IR_addDecls(x_13, x_6, x_20);
lean_dec(x_13);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim_dead", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__2;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_case", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__5;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("borrow", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__8;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("boxing", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__11;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rc", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__14;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_compiler_reuse;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expand_reset_reuse", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__18;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_8 = lean_array_size(x_4);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2(x_8, x_1, x_4);
x_10 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__3;
x_11 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__2;
lean_inc(x_9);
x_12 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_10, x_11, x_9, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_size(x_9);
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3(x_14, x_1, x_9);
x_16 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__6;
x_17 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__5;
lean_inc(x_15);
x_18 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_16, x_17, x_15, x_6, x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_size(x_15);
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4(x_20, x_1, x_15);
x_22 = l_Lean_IR_inferBorrow(x_21, x_6, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__9;
x_26 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__8;
lean_inc(x_23);
x_27 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_25, x_26, x_23, x_6, x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_IR_explicitBoxing(x_23, x_6, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__12;
x_33 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__11;
lean_inc(x_30);
x_34 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_32, x_33, x_30, x_6, x_31);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_IR_explicitRC(x_30, x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__15;
x_40 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__14;
lean_inc(x_37);
x_41 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_39, x_40, x_37, x_6, x_38);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__16;
x_44 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_6, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
x_46 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1(x_1, x_2, x_3, x_37, x_45, x_6, x_42);
return x_46;
}
else
{
size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_array_size(x_37);
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5(x_47, x_1, x_37);
x_49 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__19;
x_50 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__18;
lean_inc(x_48);
x_51 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_49, x_50, x_48, x_6, x_42);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1(x_1, x_2, x_3, x_48, x_52, x_6, x_53);
lean_dec(x_52);
return x_54;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim_dead_branches", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("push_proj", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reset_reuse", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11;
x_3 = l_Lean_Name_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3;
x_5 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2;
lean_inc(x_1);
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_4, x_5, x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = l_Lean_IR_checkDecls(x_1, x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6;
x_14 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5;
lean_inc(x_11);
x_15 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_13, x_14, x_11, x_2, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_size(x_11);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(x_17, x_18, x_11);
x_20 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9;
x_21 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8;
lean_inc(x_19);
x_22 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_20, x_21, x_19, x_2, x_16);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__16;
x_25 = l_Lean_Option_get___at_Lean_Compiler_LCNF_toConfigOptions___spec__2(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2(x_18, x_20, x_21, x_19, x_26, x_2, x_23);
return x_27;
}
else
{
size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_array_size(x_19);
x_29 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6(x_28, x_18, x_19);
x_30 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12;
x_31 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11;
lean_inc(x_29);
x_32 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_30, x_31, x_29, x_2, x_23);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2(x_18, x_20, x_21, x_29, x_33, x_2, x_34);
lean_dec(x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_compile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_ir_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_IR_compile___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(x_3, x_2, x_5);
lean_dec(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_7, 1, x_11);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_6, 0, x_19);
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ir_add_decl(x_10, x_8);
lean_ctor_set(x_6, 0, x_11);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_box(0);
x_2 = x_13;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_ir_add_decl(x_16, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_box(0);
x_2 = x_21;
x_4 = x_22;
x_6 = x_19;
goto _start;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addBoxedVersionAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_6, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_4);
x_10 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_mk(x_12);
x_14 = l_Lean_IR_explicitRC(x_13, x_2, x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_array_get_size(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_16);
x_21 = lean_box(0);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_16);
x_23 = lean_box(0);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_14);
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = lean_box(0);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(x_16, x_24, x_25, x_26, x_2, x_17);
lean_dec(x_16);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_array_get_size(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_lt(x_35, x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_34, x_34);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
lean_dec(x_32);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = 0;
x_43 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_44 = lean_box(0);
x_45 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(x_32, x_42, x_43, x_44, x_2, x_33);
lean_dec(x_32);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_4);
x_51 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_49, x_1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_54 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_mk(x_56);
x_58 = l_Lean_IR_explicitRC(x_57, x_2, x_50);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_array_get_size(x_59);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_lt(x_63, x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_59);
x_65 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_62, x_62);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_62);
lean_dec(x_59);
x_68 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_60);
return x_69;
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_61);
x_70 = 0;
x_71 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_72 = lean_box(0);
x_73 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(x_59, x_70, x_71, x_72, x_2, x_60);
lean_dec(x_59);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addBoxedVersionAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_ir_add_boxed_version(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_IR_compile___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Options_empty;
x_6 = l_Lean_IR_addBoxedVersionAux(x_2, x_5, x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
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
lean_object* initialize_Lean_Compiler_IR_CtorLayout(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Sorry(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_LLVMBindings(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_EmitLLVM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
res = initialize_Lean_Compiler_IR_CtorLayout(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Sorry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_LLVMBindings(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitLLVM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__1 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__1();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__1);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__2 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__2();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__2);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__3 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__3();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__3);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__4 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__4();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__4);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__5 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__5();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__5);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__6 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__6();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__6);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__7 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__7();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__7);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__8 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__8();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__8);
l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__9 = _init_l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__9();
lean_mark_persistent(l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5____closed__9);
if (builtin) {res = l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_compiler_reuse = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_compiler_reuse);
lean_dec_ref(res);
}l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__1 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__1);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__2 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__2);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__3 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__1___closed__3);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__1 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__1);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__2 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__2);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__3 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__3);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__4 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__4);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__5 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__5);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__6 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__6);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__7 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__7);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__8 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__8);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__9 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__9();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__9);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__10 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__10();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__10);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__11 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__11();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__11);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__12 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__12();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__12);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__13 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__13();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__13);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__14 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__14();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__14);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__15 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__15();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__15);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__16 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__16();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__16);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__17 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__17();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__17);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__18 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__18();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__18);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__19 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__19();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___lambda__2___closed__19);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12);
l_Lean_IR_compile___closed__1 = _init_l_Lean_IR_compile___closed__1();
lean_mark_persistent(l_Lean_IR_compile___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
