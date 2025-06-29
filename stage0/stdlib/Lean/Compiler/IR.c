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
static lean_object* l_Lean_IR_initFn___closed__2____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8;
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__1(size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
lean_object* l_Lean_IR_elimDeadBranches___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__5(size_t, size_t, lean_object*);
lean_object* l_Lean_IR_inferBorrow___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__2(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_IR_initFn___closed__8____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11;
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__32;
static lean_object* l_Lean_IR_initFn___closed__0____x40_Lean_Compiler_IR___hyg_5_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15;
LEAN_EXPORT lean_object* l_Lean_IR_compiler_reuse;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__2___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17;
static lean_object* l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l_Lean_IR_initFn___closed__7____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21;
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__3(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22;
static lean_object* l_Lean_IR_initFn___closed__6____x40_Lean_Compiler_IR___hyg_5_;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1;
static lean_object* l_Lean_IR_initFn___closed__1____x40_Lean_Compiler_IR___hyg_5_;
lean_object* l_Lean_IR_explicitBoxing___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_compile___closed__0;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__5____x40_Lean_Compiler_IR___hyg_5_;
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__4(size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27;
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23;
lean_object* l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_185__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26;
static lean_object* l_Lean_IR_addBoxedVersionAux___closed__0;
LEAN_EXPORT lean_object* lean_ir_add_boxed_version(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__0(size_t, size_t, lean_object*);
lean_object* lean_ir_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_IR_explicitRC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addBoxedVersionAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_compile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__33;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__0;
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_initFn____x40_Lean_Compiler_IR___hyg_5_(lean_object*);
lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_getEnv___redArg(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25;
static lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_initFn___closed__4____x40_Lean_Compiler_IR___hyg_5_;
x_2 = l_Lean_IR_initFn___closed__3____x40_Lean_Compiler_IR___hyg_5_;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
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
x_5 = l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_185__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim_dead_branches", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("push_proj", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim_dead", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_case", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("borrow", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("boxing", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rc", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_compiler_reuse;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expand_reset_reuse", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reset_reuse", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__32;
x_2 = l_Lean_IR_tracePrefixOptionName;
x_3 = l_Lean_Name_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1;
x_5 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2;
lean_inc(x_1);
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_5, x_4, x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = l_Lean_IR_checkDecls(x_1, x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_elimDeadBranches___redArg(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4;
x_14 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5;
lean_inc(x_11);
x_15 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_14, x_13, x_11, x_2, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_size(x_11);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__0(x_17, x_18, x_11);
x_20 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7;
x_87 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8;
lean_inc(x_19);
x_88 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_87, x_20, x_19, x_2, x_16);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27;
x_91 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_2, x_90);
if (x_91 == 0)
{
x_40 = x_19;
x_41 = x_2;
x_42 = x_89;
goto block_86;
}
else
{
size_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_array_size(x_19);
x_93 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__5(x_92, x_18, x_19);
x_94 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__32;
x_95 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__33;
lean_inc(x_93);
x_96 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_95, x_94, x_93, x_2, x_89);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_40 = x_93;
x_41 = x_2;
x_42 = x_97;
goto block_86;
}
block_39:
{
size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_array_size(x_21);
x_25 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__0(x_24, x_18, x_21);
x_26 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8;
lean_inc(x_25);
x_27 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_26, x_20, x_25, x_22, x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_IR_updateSorryDep(x_25, x_22, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10;
x_33 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11;
lean_inc(x_30);
x_34 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_33, x_32, x_30, x_22, x_31);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_30);
x_36 = l_Lean_IR_checkDecls(x_30, x_22, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_IR_addDecls(x_30, x_22, x_37);
lean_dec(x_30);
return x_38;
}
else
{
lean_dec(x_30);
return x_36;
}
}
block_86:
{
size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_43 = lean_array_size(x_40);
x_44 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__1(x_43, x_18, x_40);
x_45 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13;
x_46 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14;
lean_inc(x_44);
x_47 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_46, x_45, x_44, x_41, x_42);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_array_size(x_44);
x_50 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__2(x_49, x_18, x_44);
x_51 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16;
x_52 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17;
lean_inc(x_50);
x_53 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_52, x_51, x_50, x_41, x_48);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_array_size(x_50);
x_56 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__3(x_55, x_18, x_50);
x_57 = l_Lean_IR_inferBorrow___redArg(x_56, x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19;
x_61 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20;
lean_inc(x_58);
x_62 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_61, x_60, x_58, x_41, x_59);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_IR_explicitBoxing___redArg(x_58, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22;
x_68 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23;
lean_inc(x_65);
x_69 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_68, x_67, x_65, x_41, x_66);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_IR_explicitRC___redArg(x_65, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25;
x_75 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26;
lean_inc(x_72);
x_76 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_75, x_74, x_72, x_41, x_73);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27;
x_79 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_41, x_78);
if (x_79 == 0)
{
x_21 = x_72;
x_22 = x_41;
x_23 = x_77;
goto block_39;
}
else
{
size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_array_size(x_72);
x_81 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__4(x_80, x_18, x_72);
x_82 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29;
x_83 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30;
lean_inc(x_81);
x_84 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_83, x_82, x_81, x_41, x_77);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_21 = x_81;
x_22 = x_41;
x_23 = x_85;
goto block_39;
}
}
}
else
{
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_IR_0__Lean_IR_compileAux_spec__5(x_4, x_5, x_3);
return x_6;
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
static lean_object* _init_l_Lean_IR_compile___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_ir_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_IR_compile___closed__0;
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_16, 1, x_21);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_array_uget(x_1, x_2);
x_10 = lean_box(0);
x_11 = lean_ir_add_decl(x_8, x_9);
lean_ctor_set(x_5, 0, x_11);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_array_uget(x_1, x_2);
x_18 = lean_box(0);
x_19 = lean_ir_add_decl(x_15, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_18;
x_5 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_addBoxedVersionAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addBoxedVersionAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_IR_getEnv___redArg(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_1);
x_12 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_10, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_8);
x_14 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_15 = l_Lean_IR_addBoxedVersionAux___closed__0;
x_16 = lean_array_push(x_15, x_14);
x_17 = l_Lean_IR_explicitRC___redArg(x_16, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_18);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_18);
x_4 = x_19;
goto block_7;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_18);
x_4 = x_19;
goto block_7;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_box(0);
x_25 = 0;
x_26 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_27 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___redArg(x_18, x_25, x_26, x_24, x_19);
lean_dec(x_18);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_4 = x_28;
goto block_7;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
lean_inc(x_1);
x_31 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_29, x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_35 = l_Lean_IR_addBoxedVersionAux___closed__0;
x_36 = lean_array_push(x_35, x_34);
x_37 = l_Lean_IR_explicitRC___redArg(x_36, x_30);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_array_get_size(x_38);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_dec(x_38);
x_4 = x_39;
goto block_7;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_41, x_41);
if (x_43 == 0)
{
lean_dec(x_41);
lean_dec(x_38);
x_4 = x_39;
goto block_7;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_box(0);
x_45 = 0;
x_46 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_47 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___redArg(x_38, x_45, x_46, x_44, x_39);
lean_dec(x_38);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_4 = x_48;
goto block_7;
}
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_addBoxedVersionAux_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
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
return x_4;
}
}
LEAN_EXPORT lean_object* lean_ir_add_boxed_version(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_box(0);
x_4 = l_Lean_IR_compile___closed__0;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_IR_addBoxedVersionAux(x_2, x_3, x_5);
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
}l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__0 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__0);
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
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__32 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__32();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__32);
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__33 = _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__33();
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__33);
l_Lean_IR_compile___closed__0 = _init_l_Lean_IR_compile___closed__0();
lean_mark_persistent(l_Lean_IR_compile___closed__0);
l_Lean_IR_addBoxedVersionAux___closed__0 = _init_l_Lean_IR_addBoxedVersionAux___closed__0();
lean_mark_persistent(l_Lean_IR_addBoxedVersionAux___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
