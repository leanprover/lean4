// Lean compiler output
// Module: Lean.Compiler.LCNF.ExtractClosed
// Imports: Lean.Compiler.ClosedTermCache Lean.Compiler.NeverExtractAttr Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Internalize Lean.Compiler.LCNF.MonoTypes Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.ToExpr
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__3;
static lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__8;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__13;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__3;
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__4;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_get_closed_term_name(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_extractClosed___elambda__1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5;
static lean_object* l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__17;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__18;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__12;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__19;
lean_object* lean_cache_closed_term_name(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toExpr(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__7;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__6;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__1;
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Alt_getCode(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl;
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__2(lean_object*, size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__10;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__16;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6;
static lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__3(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__14;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
lean_object* l_Array_back_x21___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__15;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__1;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_extractClosed___elambda__1___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_hasNeverExtractAttribute_visit(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_ExtractClosed_visitDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 2);
x_9 = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_11, x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___spec__1(x_10, x_19, x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(x_23, x_2, x_3, x_4, x_5, x_6, x_7);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_array_get_size(x_24);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
x_32 = lean_box(0);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_29, x_29);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_29);
x_34 = lean_box(0);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_25);
x_35 = 0;
x_36 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___spec__1(x_24, x_35, x_36, x_37, x_2, x_3, x_4, x_5, x_6, x_27);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_array_get_size(x_24);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_lt(x_41, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_40, x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_40);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = lean_box(0);
x_51 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___spec__1(x_24, x_48, x_49, x_50, x_2, x_3, x_4, x_5, x_6, x_39);
return x_51;
}
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_st_ref_take(x_2, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_18);
lean_ctor_set_tag(x_9, 0);
x_22 = lean_array_push(x_20, x_9);
x_23 = lean_st_ref_set(x_2, x_22, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_18, 3);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(x_25, x_2, x_3, x_4, x_5, x_6, x_24);
lean_dec(x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
lean_dec(x_9);
x_28 = lean_st_ref_take(x_2, x_16);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_27);
x_32 = lean_array_push(x_29, x_31);
x_33 = lean_st_ref_set(x_2, x_32, x_30);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_27, 3);
lean_inc(x_35);
lean_dec(x_27);
x_36 = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(x_35, x_2, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_2 = x_26;
x_10 = x_24;
goto _start;
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__1(x_1, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
lean_dec(x_30);
x_31 = 0;
x_32 = lean_box(x_31);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_2 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_10, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_Environment_find_x3f(x_18, x_3, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_14);
x_21 = lean_box(0);
x_22 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
switch (lean_obj_tag(x_23)) {
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Expr_isForall(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_box(x_19);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_14);
x_29 = lean_box(0);
x_30 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_30;
}
}
case 6:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_23);
x_31 = lean_array_get_size(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
x_34 = lean_box(x_19);
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
else
{
size_t x_35; size_t x_36; uint8_t x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_37 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__2(x_1, x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_box(x_19);
lean_ctor_set(x_14, 0, x_38);
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_14);
x_39 = lean_box(0);
x_40 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_40;
}
}
}
default: 
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_23);
lean_free_object(x_14);
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = 0;
x_47 = l_Lean_Environment_find_x3f(x_45, x_3, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Expr_isForall(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_box(x_46);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_44);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
x_58 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
return x_58;
}
}
case 6:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_50);
x_59 = lean_array_get_size(x_1);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
x_62 = lean_box(x_46);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_44);
return x_63;
}
else
{
size_t x_64; size_t x_65; uint8_t x_66; 
x_64 = 0;
x_65 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_66 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__2(x_1, x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(x_46);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_44);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(0);
x_70 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_69, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
return x_70;
}
}
}
default: 
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_50);
x_71 = lean_box(0);
x_72 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_71, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
return x_72;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_3);
x_17 = l_Lean_hasNeverExtractAttribute_visit(x_16, x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_12);
x_18 = lean_box(0);
x_19 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__2(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_3);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
x_25 = l_Lean_hasNeverExtractAttribute_visit(x_24, x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__2(x_1, x_2, x_3, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_27;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("9223372036854775808");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
switch (lean_obj_tag(x_10)) {
case 0:
{
if (x_1 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__1;
x_16 = lean_nat_dec_le(x_15, x_14);
lean_dec(x_14);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
case 1:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
default: 
{
lean_dec(x_10);
if (x_1 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
}
case 1:
{
if (x_1 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
case 2:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_2, 2);
lean_inc(x_34);
lean_dec(x_2);
x_35 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_34);
return x_35;
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_array_get_size(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_lt(x_40, x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__3(x_37, x_1, x_36, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_37);
return x_43;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_46 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__3(x_36, x_38, x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__3(x_37, x_1, x_36, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_37);
return x_48;
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
lean_dec(x_36);
x_49 = 0;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_9);
return x_51;
}
}
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
lean_dec(x_2);
x_54 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_67 = lean_array_get_size(x_53);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_nat_dec_lt(x_68, x_67);
if (x_69 == 0)
{
uint8_t x_70; 
lean_dec(x_67);
lean_dec(x_53);
x_70 = 1;
x_58 = x_70;
x_59 = x_56;
goto block_66;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = 0;
x_72 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_73 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__1(x_53, x_71, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
lean_dec(x_53);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = 1;
x_58 = x_77;
x_59 = x_76;
goto block_66;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = 0;
x_58 = x_79;
x_59 = x_78;
goto block_66;
}
}
block_66:
{
uint8_t x_60; 
x_60 = lean_unbox(x_55);
lean_dec(x_55);
if (x_60 == 0)
{
uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_61 = 0;
x_62 = lean_box(x_61);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_57;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_box(x_58);
if (lean_is_scalar(x_57)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_57;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(x_22, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__2(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__2(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lambda__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_14, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
x_9 = x_17;
goto _start;
}
}
}
static lean_object* _init_l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 5);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__3;
lean_ctor_set(x_10, 5, x_15);
lean_ctor_set(x_10, 0, x_1);
x_16 = lean_st_ref_set(x_7, x_10, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 6);
x_28 = lean_ctor_get(x_10, 7);
x_29 = lean_ctor_get(x_10, 8);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_30 = l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__3;
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set(x_31, 4, x_26);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_27);
lean_ctor_set(x_31, 7, x_28);
lean_ctor_set(x_31, 8, x_29);
x_32 = lean_st_ref_set(x_7, x_31, x_11);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = l_Lean_Compiler_LCNF_Alt_getCode(x_13);
lean_inc(x_4);
x_17 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_15, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
x_10 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_2);
lean_inc(x_3);
x_15 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_3, x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_4);
x_19 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_23 = lean_ptr_addr(x_21);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_15, 1, x_21);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_26 = lean_ptr_addr(x_17);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_dec(x_5);
lean_ctor_set(x_15, 1, x_21);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
lean_dec(x_21);
lean_free_object(x_15);
lean_dec(x_17);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_31 = lean_ptr_addr(x_28);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_15, 1, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_35 = lean_ptr_addr(x_17);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_5);
lean_ctor_set(x_15, 1, x_28);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_28);
lean_free_object(x_15);
lean_dec(x_17);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_29);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
lean_inc(x_4);
x_41 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_46 = lean_ptr_addr(x_42);
x_47 = lean_usize_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_42);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
size_t x_50; size_t x_51; uint8_t x_52; 
x_50 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_51 = lean_ptr_addr(x_39);
x_52 = lean_usize_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_5);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_42);
if (lean_is_scalar(x_44)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_44;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_43);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_42);
lean_dec(x_39);
if (lean_is_scalar(x_44)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_44;
}
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_43);
return x_55;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_closed", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 3);
lean_inc(x_12);
x_13 = 1;
lean_inc(x_12);
x_14 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(x_13, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_10);
x_18 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_22 = lean_ptr_addr(x_20);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
}
else
{
size_t x_28; uint8_t x_29; 
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_1, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 0);
lean_dec(x_32);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_33; 
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_18, 0, x_33);
return x_18;
}
}
else
{
lean_dec(x_20);
lean_dec(x_9);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_37 = lean_ptr_addr(x_34);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_39 = x_1;
} else {
 lean_dec_ref(x_1);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
else
{
size_t x_42; uint8_t x_43; 
x_42 = lean_ptr_addr(x_9);
x_43 = lean_usize_dec_eq(x_42, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_44 = x_1;
} else {
 lean_dec_ref(x_1);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_9);
lean_ctor_set(x_45, 1, x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_35);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_34);
lean_dec(x_9);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_35);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_dec(x_14);
x_49 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1;
x_50 = lean_st_mk_ref(x_49, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(x_12, x_51, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_12);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_51, x_54);
lean_dec(x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Array_reverse___rarg(x_56);
lean_inc(x_9);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_9);
x_60 = lean_array_push(x_58, x_59);
x_61 = lean_array_size(x_60);
x_62 = 0;
x_63 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
x_64 = lean_st_mk_ref(x_63, x_57);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__1(x_61, x_62, x_60, x_65, x_4, x_5, x_6, x_7, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_get(x_65, x_69);
lean_dec(x_65);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl;
x_73 = l_Array_back_x21___rarg(x_72, x_68);
x_74 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_73);
lean_dec(x_73);
x_75 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_Compiler_LCNF_attachCodeDecls(x_68, x_75);
lean_dec(x_68);
x_77 = lean_box(0);
x_78 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5;
lean_inc(x_76);
x_79 = l_Lean_Compiler_LCNF_Code_toExpr(x_76, x_78);
x_80 = lean_st_ref_get(x_7, x_71);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_79);
lean_inc(x_83);
x_84 = lean_get_closed_term_name(x_83, x_79);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_85 = lean_st_ref_get(x_3, x_82);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = lean_array_get_size(x_86);
lean_dec(x_86);
x_90 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7;
x_91 = lean_name_append_index_after(x_90, x_89);
x_92 = l_Lean_Name_append(x_88, x_91);
lean_inc(x_92);
x_93 = lean_cache_closed_term_name(x_83, x_79, x_92);
x_94 = l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2(x_93, x_2, x_3, x_4, x_5, x_6, x_7, x_87);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_76);
x_97 = 0;
x_98 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8;
lean_inc(x_92);
x_99 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_99, 0, x_92);
lean_ctor_set(x_99, 1, x_77);
lean_ctor_set(x_99, 2, x_11);
lean_ctor_set(x_99, 3, x_78);
lean_ctor_set(x_99, 4, x_96);
lean_ctor_set(x_99, 5, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*6, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*6 + 1, x_13);
lean_inc(x_99);
x_100 = l_Lean_Compiler_LCNF_Decl_saveMono(x_99, x_6, x_7, x_95);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_st_ref_take(x_3, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_array_push(x_103, x_99);
x_106 = lean_st_ref_set(x_3, x_105, x_104);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___lambda__1(x_77, x_78, x_9, x_10, x_1, x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_11);
x_109 = lean_ctor_get(x_84, 0);
lean_inc(x_109);
lean_dec(x_84);
x_110 = l_Lean_Compiler_LCNF_eraseCode(x_76, x_4, x_5, x_6, x_7, x_82);
lean_dec(x_76);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___lambda__1(x_77, x_78, x_9, x_10, x_1, x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_111);
return x_112;
}
}
}
case 1:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 4);
lean_inc(x_115);
lean_inc(x_2);
x_116 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_113, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 2);
lean_inc(x_120);
lean_inc(x_113);
x_121 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_113, x_119, x_120, x_117, x_4, x_5, x_6, x_7, x_118);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_114);
x_124 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_123);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; size_t x_127; size_t x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ptr_addr(x_114);
lean_dec(x_114);
x_128 = lean_ptr_addr(x_126);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
uint8_t x_130; 
lean_dec(x_113);
x_130 = !lean_is_exclusive(x_1);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_1, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_1, 0);
lean_dec(x_132);
lean_ctor_set(x_1, 1, x_126);
lean_ctor_set(x_1, 0, x_122);
lean_ctor_set(x_124, 0, x_1);
return x_124;
}
else
{
lean_object* x_133; 
lean_dec(x_1);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_122);
lean_ctor_set(x_133, 1, x_126);
lean_ctor_set(x_124, 0, x_133);
return x_124;
}
}
else
{
size_t x_134; size_t x_135; uint8_t x_136; 
x_134 = lean_ptr_addr(x_113);
lean_dec(x_113);
x_135 = lean_ptr_addr(x_122);
x_136 = lean_usize_dec_eq(x_134, x_135);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_1);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_1, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_1, 0);
lean_dec(x_139);
lean_ctor_set(x_1, 1, x_126);
lean_ctor_set(x_1, 0, x_122);
lean_ctor_set(x_124, 0, x_1);
return x_124;
}
else
{
lean_object* x_140; 
lean_dec(x_1);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_122);
lean_ctor_set(x_140, 1, x_126);
lean_ctor_set(x_124, 0, x_140);
return x_124;
}
}
else
{
lean_dec(x_126);
lean_dec(x_122);
lean_ctor_set(x_124, 0, x_1);
return x_124;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; size_t x_143; size_t x_144; uint8_t x_145; 
x_141 = lean_ctor_get(x_124, 0);
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_124);
x_143 = lean_ptr_addr(x_114);
lean_dec(x_114);
x_144 = lean_ptr_addr(x_141);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_113);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_146 = x_1;
} else {
 lean_dec_ref(x_1);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_122);
lean_ctor_set(x_147, 1, x_141);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
else
{
size_t x_149; size_t x_150; uint8_t x_151; 
x_149 = lean_ptr_addr(x_113);
lean_dec(x_113);
x_150 = lean_ptr_addr(x_122);
x_151 = lean_usize_dec_eq(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_152 = x_1;
} else {
 lean_dec_ref(x_1);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_122);
lean_ctor_set(x_153, 1, x_141);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_142);
return x_154;
}
else
{
lean_object* x_155; 
lean_dec(x_141);
lean_dec(x_122);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_1);
lean_ctor_set(x_155, 1, x_142);
return x_155;
}
}
}
}
case 2:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_156 = lean_ctor_get(x_1, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_1, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 4);
lean_inc(x_158);
lean_inc(x_2);
x_159 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_158, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_156, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_156, 2);
lean_inc(x_163);
lean_inc(x_156);
x_164 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_156, x_162, x_163, x_160, x_4, x_5, x_6, x_7, x_161);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_157);
x_167 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_166);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; size_t x_170; size_t x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ptr_addr(x_157);
lean_dec(x_157);
x_171 = lean_ptr_addr(x_169);
x_172 = lean_usize_dec_eq(x_170, x_171);
if (x_172 == 0)
{
uint8_t x_173; 
lean_dec(x_156);
x_173 = !lean_is_exclusive(x_1);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_1, 1);
lean_dec(x_174);
x_175 = lean_ctor_get(x_1, 0);
lean_dec(x_175);
lean_ctor_set(x_1, 1, x_169);
lean_ctor_set(x_1, 0, x_165);
lean_ctor_set(x_167, 0, x_1);
return x_167;
}
else
{
lean_object* x_176; 
lean_dec(x_1);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_165);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_167, 0, x_176);
return x_167;
}
}
else
{
size_t x_177; size_t x_178; uint8_t x_179; 
x_177 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_178 = lean_ptr_addr(x_165);
x_179 = lean_usize_dec_eq(x_177, x_178);
if (x_179 == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_1);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_1, 1);
lean_dec(x_181);
x_182 = lean_ctor_get(x_1, 0);
lean_dec(x_182);
lean_ctor_set(x_1, 1, x_169);
lean_ctor_set(x_1, 0, x_165);
lean_ctor_set(x_167, 0, x_1);
return x_167;
}
else
{
lean_object* x_183; 
lean_dec(x_1);
x_183 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_183, 0, x_165);
lean_ctor_set(x_183, 1, x_169);
lean_ctor_set(x_167, 0, x_183);
return x_167;
}
}
else
{
lean_dec(x_169);
lean_dec(x_165);
lean_ctor_set(x_167, 0, x_1);
return x_167;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; size_t x_186; size_t x_187; uint8_t x_188; 
x_184 = lean_ctor_get(x_167, 0);
x_185 = lean_ctor_get(x_167, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_167);
x_186 = lean_ptr_addr(x_157);
lean_dec(x_157);
x_187 = lean_ptr_addr(x_184);
x_188 = lean_usize_dec_eq(x_186, x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_156);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_189 = x_1;
} else {
 lean_dec_ref(x_1);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(2, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_165);
lean_ctor_set(x_190, 1, x_184);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_185);
return x_191;
}
else
{
size_t x_192; size_t x_193; uint8_t x_194; 
x_192 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_193 = lean_ptr_addr(x_165);
x_194 = lean_usize_dec_eq(x_192, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_195 = x_1;
} else {
 lean_dec_ref(x_1);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(2, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_165);
lean_ctor_set(x_196, 1, x_184);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_185);
return x_197;
}
else
{
lean_object* x_198; 
lean_dec(x_184);
lean_dec(x_165);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_1);
lean_ctor_set(x_198, 1, x_185);
return x_198;
}
}
}
}
case 4:
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_1, 0);
lean_inc(x_199);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; size_t x_205; size_t x_206; lean_object* x_207; uint8_t x_208; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = lean_ctor_get(x_199, 1);
x_203 = lean_ctor_get(x_199, 2);
x_204 = lean_ctor_get(x_199, 3);
x_205 = lean_array_size(x_204);
x_206 = 0;
lean_inc(x_204);
x_207 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__3(x_205, x_206, x_204, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; size_t x_210; size_t x_211; uint8_t x_212; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ptr_addr(x_204);
lean_dec(x_204);
x_211 = lean_ptr_addr(x_209);
x_212 = lean_usize_dec_eq(x_210, x_211);
if (x_212 == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_1);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_1, 0);
lean_dec(x_214);
lean_ctor_set(x_199, 3, x_209);
lean_ctor_set(x_207, 0, x_1);
return x_207;
}
else
{
lean_object* x_215; 
lean_dec(x_1);
lean_ctor_set(x_199, 3, x_209);
x_215 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_215, 0, x_199);
lean_ctor_set(x_207, 0, x_215);
return x_207;
}
}
else
{
lean_dec(x_209);
lean_free_object(x_199);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_ctor_set(x_207, 0, x_1);
return x_207;
}
}
else
{
lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_207, 0);
x_217 = lean_ctor_get(x_207, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_207);
x_218 = lean_ptr_addr(x_204);
lean_dec(x_204);
x_219 = lean_ptr_addr(x_216);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_221 = x_1;
} else {
 lean_dec_ref(x_1);
 x_221 = lean_box(0);
}
lean_ctor_set(x_199, 3, x_216);
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(4, 1, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_199);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_217);
return x_223;
}
else
{
lean_object* x_224; 
lean_dec(x_216);
lean_free_object(x_199);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_1);
lean_ctor_set(x_224, 1, x_217);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; size_t x_229; size_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; size_t x_235; size_t x_236; uint8_t x_237; 
x_225 = lean_ctor_get(x_199, 0);
x_226 = lean_ctor_get(x_199, 1);
x_227 = lean_ctor_get(x_199, 2);
x_228 = lean_ctor_get(x_199, 3);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_199);
x_229 = lean_array_size(x_228);
x_230 = 0;
lean_inc(x_228);
x_231 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__3(x_229, x_230, x_228, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
x_235 = lean_ptr_addr(x_228);
lean_dec(x_228);
x_236 = lean_ptr_addr(x_232);
x_237 = lean_usize_dec_eq(x_235, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_238 = x_1;
} else {
 lean_dec_ref(x_1);
 x_238 = lean_box(0);
}
x_239 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_239, 0, x_225);
lean_ctor_set(x_239, 1, x_226);
lean_ctor_set(x_239, 2, x_227);
lean_ctor_set(x_239, 3, x_232);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(4, 1, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
if (lean_is_scalar(x_234)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_234;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_233);
return x_241;
}
else
{
lean_object* x_242; 
lean_dec(x_232);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
if (lean_is_scalar(x_234)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_234;
}
lean_ctor_set(x_242, 0, x_1);
lean_ctor_set(x_242, 1, x_233);
return x_242;
}
}
}
default: 
{
lean_object* x_243; 
lean_dec(x_2);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_1);
lean_ctor_set(x_243, 1, x_8);
return x_243;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__3(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_ExtractClosed_visitDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_apply_8(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_apply_8(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
x_16 = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__1;
x_17 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_ExtractClosed_visitDecl___spec__1(x_16, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 4, x_19);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 4, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_1);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_1, 3);
x_31 = lean_ctor_get(x_1, 4);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_34 = lean_ctor_get(x_1, 5);
lean_inc(x_34);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_35 = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__1;
x_36 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at_Lean_Compiler_LCNF_ExtractClosed_visitDecl___spec__1(x_35, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_40, 2, x_29);
lean_ctor_set(x_40, 3, x_30);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_32);
lean_ctor_set_uint8(x_40, sizeof(void*)*6 + 1, x_33);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1;
x_11 = lean_st_mk_ref(x_10, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(x_1, x_9, x_12, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_array_push(x_19, x_15);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_array_push(x_21, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_12);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_extractClosed___elambda__1___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Decl_extractClosed(x_12, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_append___rarg(x_5, x_14);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_16;
x_10 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extract_closed", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__1;
x_2 = l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__3;
x_9 = 1;
x_10 = l_Lean_KVMap_getBool(x_7, x_8, x_9);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5;
lean_inc(x_1);
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_extractClosed___elambda__1___spec__1(x_1, x_1, x_20, x_21, x_22, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_23;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extractClosed", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_extractClosed___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_extractClosed___elambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 1;
x_3 = 0;
x_4 = l_Lean_Compiler_LCNF_extractClosed___closed__2;
x_5 = l_Lean_Compiler_LCNF_extractClosed___closed__3;
x_6 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 2, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_extractClosed___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_extractClosed___elambda__1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_extractClosed___elambda__1___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__1;
x_2 = l_Lean_Compiler_LCNF_extractClosed___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__4;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__13;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ExtractClosed", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__16;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__18;
x_2 = lean_unsigned_to_nat(1835u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__2;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__19;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_MonoTypes(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ExtractClosed(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ClosedTermCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NeverExtractAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__1 = _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__1);
l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__1 = _init_l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__1();
lean_mark_persistent(l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__1);
l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__2 = _init_l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__2();
lean_mark_persistent(l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__2);
l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__3 = _init_l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__3();
lean_mark_persistent(l_Lean_setEnv___at_Lean_Compiler_LCNF_ExtractClosed_visitCode___spec__2___closed__3);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8);
l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__1 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__1);
l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__1);
l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__2);
l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__3 = _init_l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___elambda__1___closed__3);
l_Lean_Compiler_LCNF_extractClosed___closed__1 = _init_l_Lean_Compiler_LCNF_extractClosed___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___closed__1);
l_Lean_Compiler_LCNF_extractClosed___closed__2 = _init_l_Lean_Compiler_LCNF_extractClosed___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___closed__2);
l_Lean_Compiler_LCNF_extractClosed___closed__3 = _init_l_Lean_Compiler_LCNF_extractClosed___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___closed__3);
l_Lean_Compiler_LCNF_extractClosed___closed__4 = _init_l_Lean_Compiler_LCNF_extractClosed___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___closed__4);
l_Lean_Compiler_LCNF_extractClosed = _init_l_Lean_Compiler_LCNF_extractClosed();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__17);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__18 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__18);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__19 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835____closed__19);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1835_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
