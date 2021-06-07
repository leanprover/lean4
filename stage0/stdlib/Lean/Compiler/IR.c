// Lean compiler output
// Module: Lean.Compiler.IR
// Imports: Init Lean.Compiler.IR.Basic Lean.Compiler.IR.Format Lean.Compiler.IR.CompilerM Lean.Compiler.IR.PushProj Lean.Compiler.IR.ElimDeadVars Lean.Compiler.IR.SimpCase Lean.Compiler.IR.ResetReuse Lean.Compiler.IR.NormIds Lean.Compiler.IR.Checker Lean.Compiler.IR.Borrow Lean.Compiler.IR.Boxing Lean.Compiler.IR.RC Lean.Compiler.IR.ExpandResetReuse Lean.Compiler.IR.UnboxResult Lean.Compiler.IR.ElimDeadBranches Lean.Compiler.IR.EmitC Lean.Compiler.IR.CtorLayout Lean.Compiler.IR.Sorry
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
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24;
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_ir_add_boxed_version(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_IR_addBoxedVersionAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2(size_t, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_compile_match__1(lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Lean_IR_explicitRC(lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6;
extern lean_object* l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_597____closed__2;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25;
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4(size_t, size_t, lean_object*);
lean_object* lean_ir_compile(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3;
lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_71____closed__2;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2;
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
lean_object* l_Lean_IR_elimDeadBranches(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_updateSorryDep(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23;
lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(size_t, size_t, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6(size_t, size_t, lean_object*);
lean_object* l_Lean_IR_compile_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19;
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_IR_Decl_pushProj(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_IR_Decl_insertResetReuse(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_IR_Decl_elimDead(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_IR_Decl_simpCase(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_IR_Decl_normalizeIds(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_IR_Decl_expandResetReuse(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_597____closed__2;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("elim_dead_branches");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("push_proj");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("reset_reuse");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("elim_dead");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("simp_case");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("borrow");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("boxing");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("rc");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("expand_reset_reuse");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("result");\
__INIT_VAR__ = x_1; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30_end: ((void) 0);}
#define _init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_IR_tracePrefixOptionName;\
x_2 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30;\
x_3 = l_Lean_Name_append(x_1, x_2);\
__INIT_VAR__ = x_3; goto l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31_end;\
}\
l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31_end: ((void) 0);}
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1;
x_5 = l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_597____closed__2;
lean_inc(x_1);
x_6 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_4, x_5, x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_1);
x_8 = l_Lean_IR_checkDecls(x_1, x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4;
x_14 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3;
lean_inc(x_11);
x_15 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_13, x_14, x_11, x_2, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_get_size(x_11);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = x_11;
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(x_18, x_19, x_20);
x_22 = x_21;
x_23 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7;
x_24 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6;
lean_inc(x_22);
x_25 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_23, x_24, x_22, x_2, x_16);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_array_get_size(x_22);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = x_22;
x_30 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2(x_28, x_19, x_29);
x_31 = x_30;
x_32 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10;
x_33 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9;
lean_inc(x_31);
x_34 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_32, x_33, x_31, x_2, x_26);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_array_get_size(x_31);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = x_31;
x_39 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3(x_37, x_19, x_38);
x_40 = x_39;
x_41 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13;
x_42 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12;
lean_inc(x_40);
x_43 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_41, x_42, x_40, x_2, x_35);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_array_get_size(x_40);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = x_40;
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4(x_46, x_19, x_47);
x_49 = x_48;
x_50 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16;
x_51 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15;
lean_inc(x_49);
x_52 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_50, x_51, x_49, x_2, x_44);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_array_get_size(x_49);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = x_49;
x_57 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5(x_55, x_19, x_56);
x_58 = x_57;
x_59 = l_Lean_IR_inferBorrow(x_58, x_2, x_53);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19;
x_63 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18;
lean_inc(x_60);
x_64 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_62, x_63, x_60, x_2, x_61);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_IR_explicitBoxing(x_60, x_2, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22;
x_70 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21;
lean_inc(x_67);
x_71 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_69, x_70, x_67, x_2, x_68);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_IR_explicitRC(x_67, x_2, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25;
x_77 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24;
lean_inc(x_74);
x_78 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_76, x_77, x_74, x_2, x_75);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_array_get_size(x_74);
x_81 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_82 = x_74;
x_83 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6(x_81, x_19, x_82);
x_84 = x_83;
x_85 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28;
x_86 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27;
lean_inc(x_84);
x_87 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_85, x_86, x_84, x_2, x_79);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_array_get_size(x_84);
x_90 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_91 = x_84;
x_92 = l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1(x_90, x_19, x_91);
x_93 = x_92;
lean_inc(x_93);
x_94 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_23, x_24, x_93, x_2, x_88);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_IR_updateSorryDep(x_93, x_2, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31;
x_100 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30;
lean_inc(x_97);
x_101 = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(x_99, x_100, x_97, x_2, x_98);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
lean_inc(x_97);
x_103 = l_Lean_IR_checkDecls(x_97, x_2, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Lean_IR_addDecls(x_97, x_2, x_104);
lean_dec(x_97);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_97);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_103);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_8);
if (x_110 == 0)
{
return x_8;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_8, 0);
x_112 = lean_ctor_get(x_8, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_8);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Compiler_IR_0__Lean_IR_compileAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_compile_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_IR_compile_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_compile_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* lean_ir_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Lean_Compiler_IR_0__Lean_IR_compileAux(x_3, x_2, x_5);
lean_dec(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_2 == x_3;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = l_Lean_IR_declMapExt;
x_12 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_11, x_10, x_8);
lean_ctor_set(x_6, 0, x_12);
x_13 = 1;
x_14 = x_2 + x_13;
x_15 = lean_box(0);
x_2 = x_14;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = l_Lean_IR_declMapExt;
x_20 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_19, x_17, x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = 1;
x_23 = x_2 + x_22;
x_24 = lean_box(0);
x_2 = x_23;
x_4 = x_24;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
}
lean_object* l_Lean_IR_addBoxedVersionAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_free_object(x_4);
x_10 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_11 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Lean_IR_explicitRC(x_12, x_2, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_array_get_size(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_15);
x_20 = lean_box(0);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_17, x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
x_22 = lean_box(0);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_free_object(x_13);
x_23 = 0;
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(x_15, x_23, x_24, x_25, x_2, x_16);
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_array_get_size(x_31);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_33, x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_31);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_43 = lean_box(0);
x_44 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(x_31, x_41, x_42, x_43, x_2, x_32);
lean_dec(x_31);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_48, x_1);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_53 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_54 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
x_55 = lean_array_push(x_54, x_53);
x_56 = l_Lean_IR_explicitRC(x_55, x_2, x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_array_get_size(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_nat_dec_lt(x_61, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_57);
x_63 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_60, x_60);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
lean_dec(x_57);
x_66 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_58);
return x_67;
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_59);
x_68 = 0;
x_69 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_70 = lean_box(0);
x_71 = l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1(x_57, x_68, x_69, x_70, x_2, x_58);
lean_dec(x_57);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addBoxedVersionAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* lean_ir_add_boxed_version(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Array_empty___closed__1;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Lean_Compiler_IR_PushProj(lean_object*);
lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(lean_object*);
lean_object* initialize_Lean_Compiler_IR_SimpCase(lean_object*);
lean_object* initialize_Lean_Compiler_IR_ResetReuse(lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Checker(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Borrow(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Boxing(lean_object*);
lean_object* initialize_Lean_Compiler_IR_RC(lean_object*);
lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(lean_object*);
lean_object* initialize_Lean_Compiler_IR_UnboxResult(lean_object*);
lean_object* initialize_Lean_Compiler_IR_ElimDeadBranches(lean_object*);
lean_object* initialize_Lean_Compiler_IR_EmitC(lean_object*);
lean_object* initialize_Lean_Compiler_IR_CtorLayout(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Sorry(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_IR(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_PushProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ElimDeadVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_SimpCase(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ResetReuse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Checker(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Borrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Boxing(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_RC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ExpandResetReuse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_UnboxResult(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ElimDeadBranches(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CtorLayout(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Sorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__1);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__2);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__3);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__4);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__5);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__6);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__7);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__8);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__9);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__10);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__11);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__12);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__13);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__14);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__15);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__16);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__17);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__18);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__19);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__20);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__21);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__22);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__23);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__24);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__25);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__26);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__27);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__28);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__29);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__30);
_init_l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31);
lean_mark_persistent(l___private_Lean_Compiler_IR_0__Lean_IR_compileAux___closed__31);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
