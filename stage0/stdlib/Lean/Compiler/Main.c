// Lean compiler output
// Module: Lean.Compiler.Main
// Imports: Init Lean.Compiler.Decl Lean.Compiler.TerminalCases Lean.Compiler.CSE Lean.Compiler.Stage1 Lean.Compiler.Simp
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
lean_object* l_Lean_Compiler_toDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__1;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__1;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__9;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__7;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__8;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__15;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__22;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__17;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__14;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__5;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_checkpoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__18;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__3;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__3;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__15;
lean_object* l_Lean_Compiler_Decl_mapValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2___closed__1;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__5;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldGenerateCode___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_compileStage1Impl___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldGenerateCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__2;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__13;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__21;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__23;
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__13;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_Decl_cse___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_compileStage1Impl___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__4;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_checkpoint___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_compile_stage1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__4;
static lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode_isCompIrrelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_checkpoint(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__9;
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_checkpoint___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__16;
lean_object* l_Lean_Compiler_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_Decl_check(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__11;
static lean_object* l_Lean_Compiler_compile___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2;
static lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__19;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__11;
lean_object* l_Lean_Compiler_saveStage1Decls(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__12;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___closed__7;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_Decl_terminalCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___closed__3;
extern lean_object* l_Lean_Expr_instBEqExpr;
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___closed__2;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__10;
static lean_object* l_Lean_Compiler_shouldGenerateCode___closed__20;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___closed__8;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__8;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode_isCompIrrelevant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_11 = l_Lean_Meta_isProp(x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_isTypeFormerType(x_10, x_2, x_3, x_4, x_5, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldGenerateCode___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_is_matcher(x_8, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_is_matcher(x_13, x_1);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_shouldGenerateCode___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldGenerateCode___spec__1(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Compiler_shouldGenerateCode___lambda__2___closed__1;
x_11 = lean_box(0);
x_12 = lean_apply_4(x_10, x_11, x_3, x_4, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_2);
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 2;
lean_inc(x_1);
x_12 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_10, x_11, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_6);
x_13 = lean_box(0);
x_14 = l_Lean_Compiler_shouldGenerateCode___lambda__2(x_1, x_13, x_3, x_4, x_9);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 2;
lean_inc(x_1);
x_21 = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrAux(x_19, x_20, x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Compiler_shouldGenerateCode___lambda__2(x_1, x_22, x_3, x_4, x_18);
return x_23;
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_3);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_3);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_3);
lean_ctor_set_uint8(x_5, 12, x_3);
lean_ctor_set_uint8(x_5, 13, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_shouldGenerateCode___closed__6;
x_3 = l_Lean_Compiler_shouldGenerateCode___closed__5;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__4;
x_2 = l_Lean_Compiler_shouldGenerateCode___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_shouldGenerateCode___closed__1;
x_3 = l_Lean_Compiler_shouldGenerateCode___closed__8;
x_4 = l_Lean_Compiler_shouldGenerateCode___closed__9;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_shouldGenerateCode___closed__11;
x_3 = l_Lean_Compiler_shouldGenerateCode___closed__12;
x_4 = l_Lean_Compiler_shouldGenerateCode___closed__13;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_shouldGenerateCode___closed__15;
x_2 = l_Lean_Compiler_shouldGenerateCode___closed__17;
x_3 = l_Lean_Compiler_shouldGenerateCode___closed__18;
x_4 = l_Lean_Compiler_shouldGenerateCode___closed__21;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_shouldGenerateCode___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_shouldGenerateCode___closed__14;
x_3 = l_Lean_Compiler_shouldGenerateCode___closed__22;
x_4 = l_Lean_Compiler_shouldGenerateCode___closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_shouldGenerateCode___closed__23;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_shouldGenerateCode___closed__10;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
lean_inc(x_1);
x_12 = l_Lean_Compiler_shouldGenerateCode_isCompIrrelevant(x_1, x_11, x_9, x_2, x_3, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_3, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_9, x_16);
lean_dec(x_9);
x_18 = lean_unbox(x_13);
lean_dec(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Compiler_shouldGenerateCode___lambda__3(x_1, x_20, x_2, x_3, x_19);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
lean_dec(x_23);
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldGenerateCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isMatcher___at_Lean_Compiler_shouldGenerateCode___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_shouldGenerateCode___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_shouldGenerateCode___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_shouldGenerateCode___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1___closed__1;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_2, 2);
x_12 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_10, x_11, x_1);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_2, 2);
x_17 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_14, x_16, x_1);
lean_dec(x_14);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_checkpoint___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_11, 3);
x_15 = l_Lean_Compiler_shouldGenerateCode___closed__9;
x_16 = 0;
x_17 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_16);
lean_inc(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Std_PersistentArray_push___rarg(x_14, x_18);
lean_ctor_set(x_11, 3, x_19);
x_20 = lean_st_ref_set(x_4, x_11, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
x_30 = lean_ctor_get(x_11, 3);
x_31 = lean_ctor_get(x_11, 4);
x_32 = lean_ctor_get(x_11, 5);
x_33 = lean_ctor_get(x_11, 6);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_34 = l_Lean_Compiler_shouldGenerateCode___closed__9;
x_35 = 0;
x_36 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_8);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_35);
lean_inc(x_6);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Std_PersistentArray_push___rarg(x_30, x_37);
x_39 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_29);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_31);
lean_ctor_set(x_39, 5, x_32);
lean_ctor_set(x_39, 6, x_33);
x_40 = lean_st_ref_set(x_4, x_39, x_12);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_Decl_check(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pp", 2);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("motives", 7);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__4;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pi", 2);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=\n", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_6);
x_12 = lean_array_uget(x_3, x_5);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2;
lean_inc(x_1);
x_21 = l_Lean_Name_append(x_20, x_1);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 7);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 8);
lean_inc(x_30);
x_31 = lean_ctor_get(x_7, 9);
lean_inc(x_31);
x_32 = lean_ctor_get(x_7, 10);
lean_inc(x_32);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__8;
x_34 = 0;
x_35 = l_Lean_KVMap_setBool(x_24, x_33, x_34);
x_36 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set(x_36, 4, x_26);
lean_ctor_set(x_36, 5, x_27);
lean_ctor_set(x_36, 6, x_28);
lean_ctor_set(x_36, 7, x_29);
lean_ctor_set(x_36, 8, x_30);
lean_ctor_set(x_36, 9, x_31);
lean_ctor_set(x_36, 10, x_32);
lean_inc(x_21);
x_37 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1(x_21, x_36, x_8, x_9);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
lean_inc(x_8);
x_41 = l_Lean_Compiler_Decl_check(x_12, x_2, x_36, x_8, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__9;
x_13 = x_43;
x_14 = x_42;
goto block_19;
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = lean_ctor_get(x_12, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_12, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_12, 3);
lean_inc(x_51);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__11;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__13;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_50);
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__15;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_51);
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_53);
x_64 = l_Lean_addTrace___at_Lean_Compiler_checkpoint___spec__2(x_21, x_63, x_36, x_8, x_48);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
lean_inc(x_8);
x_66 = l_Lean_Compiler_Decl_check(x_12, x_2, x_36, x_8, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__9;
x_13 = x_68;
x_14 = x_67;
goto block_19;
}
else
{
uint8_t x_69; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_15;
x_9 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkpoint(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(0);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3(x_1, x_3, x_2, x_8, x_9, x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_checkpoint___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at_Lean_Compiler_checkpoint___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___lambda__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3(x_1, x_10, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkpoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Compiler_checkpoint(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Compiler_toDecl(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_11, x_2, x_13);
x_2 = x_16;
x_3 = x_17;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Decl_terminalCases___lambda__1), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Compiler_Decl_mapValue(x_9, x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_11, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Compiler_Decl_simp(x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_11, x_2, x_13);
x_2 = x_16;
x_3 = x_17;
x_6 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_Decl_cse___lambda__1), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Compiler_Decl_mapValue(x_9, x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_11, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_compileStage1Impl___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_9);
x_10 = l_Lean_Compiler_shouldGenerateCode(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_array_push(x_4, x_9);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_18;
x_7 = x_17;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("init", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("terminalCases", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cse", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__1(x_7, x_8, x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__2;
x_13 = 0;
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Compiler_checkpoint(x_12, x_10, x_13, x_3, x_4, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_array_get_size(x_10);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2(x_17, x_8, x_10, x_3, x_4, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__4;
x_22 = 1;
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Compiler_checkpoint(x_21, x_19, x_22, x_3, x_4, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_array_get_size(x_19);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__3(x_26, x_8, x_19, x_3, x_4, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__6;
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Compiler_checkpoint(x_30, x_28, x_22, x_3, x_4, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_array_get_size(x_28);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4(x_34, x_8, x_28, x_3, x_4, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__8;
lean_inc(x_4);
lean_inc(x_3);
x_39 = l_Lean_Compiler_checkpoint(x_38, x_36, x_22, x_3, x_4, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_36);
x_41 = l_Lean_Compiler_saveStage1Decls(x_36, x_3, x_4, x_40);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_36);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_36);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_35, 0);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_35);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_31);
if (x_54 == 0)
{
return x_31;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
return x_27;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_27, 0);
x_60 = lean_ctor_get(x_27, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_27);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_23);
if (x_62 == 0)
{
return x_23;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_23, 0);
x_64 = lean_ctor_get(x_23, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_23);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_4);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
return x_18;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_18, 0);
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_18);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_14);
if (x_70 == 0)
{
return x_14;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_14, 0);
x_72 = lean_ctor_get(x_14, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_14);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_9);
if (x_74 == 0)
{
return x_9;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_9, 0);
x_76 = lean_ctor_get(x_9, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_9);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* lean_compile_stage1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_1);
x_16 = l_Lean_Compiler_shouldGenerateCode___closed__9;
x_5 = x_16;
x_6 = x_4;
goto block_12;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_13);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_1);
x_18 = l_Lean_Compiler_shouldGenerateCode___closed__9;
x_5 = x_18;
x_6 = x_4;
goto block_12;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_21 = l_Lean_Compiler_shouldGenerateCode___closed__9;
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_compileStage1Impl___spec__5(x_1, x_19, x_20, x_21, x_2, x_3, x_4);
lean_dec(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_5 = x_23;
x_6 = x_24;
goto block_12;
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
block_12:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___rarg(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Compiler_compileStage1Impl___lambda__1(x_5, x_8, x_2, x_3, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = l_Lean_Compiler_shouldGenerateCode___closed__9;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__1(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__3(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_compileStage1Impl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_compileStage1Impl___spec__5(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compileStage1Impl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_compileStage1Impl___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_3, x_4, x_5);
x_8 = l_Lean_profileitIOUnsafe___rarg(x_1, x_2, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_compile_stage1(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_compile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("compiler new", 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_compile___lambda__1), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_compile___closed__1;
x_8 = l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg(x_7, x_5, x_6, x_2, x_3, x_4);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_profileitM___at_Lean_Compiler_compile___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2;
x_2 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2;
x_2 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2;
x_2 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2;
x_2 = l_Lean_Compiler_compileStage1Impl___lambda__1___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2;
x_3 = 0;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__1;
x_7 = 1;
x_8 = l_Lean_registerTraceClass(x_6, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__2;
x_11 = l_Lean_registerTraceClass(x_10, x_7, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__3;
x_14 = l_Lean_registerTraceClass(x_13, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__4;
x_17 = l_Lean_registerTraceClass(x_16, x_7, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Decl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_TerminalCases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CSE(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Stage1(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Decl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_TerminalCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSE(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Stage1(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_shouldGenerateCode___lambda__2___closed__1 = _init_l_Lean_Compiler_shouldGenerateCode___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___lambda__2___closed__1);
l_Lean_Compiler_shouldGenerateCode___closed__1 = _init_l_Lean_Compiler_shouldGenerateCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__1);
l_Lean_Compiler_shouldGenerateCode___closed__2 = _init_l_Lean_Compiler_shouldGenerateCode___closed__2();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__2);
l_Lean_Compiler_shouldGenerateCode___closed__3 = _init_l_Lean_Compiler_shouldGenerateCode___closed__3();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__3);
l_Lean_Compiler_shouldGenerateCode___closed__4 = _init_l_Lean_Compiler_shouldGenerateCode___closed__4();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__4);
l_Lean_Compiler_shouldGenerateCode___closed__5 = _init_l_Lean_Compiler_shouldGenerateCode___closed__5();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__5);
l_Lean_Compiler_shouldGenerateCode___closed__6 = _init_l_Lean_Compiler_shouldGenerateCode___closed__6();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__6);
l_Lean_Compiler_shouldGenerateCode___closed__7 = _init_l_Lean_Compiler_shouldGenerateCode___closed__7();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__7);
l_Lean_Compiler_shouldGenerateCode___closed__8 = _init_l_Lean_Compiler_shouldGenerateCode___closed__8();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__8);
l_Lean_Compiler_shouldGenerateCode___closed__9 = _init_l_Lean_Compiler_shouldGenerateCode___closed__9();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__9);
l_Lean_Compiler_shouldGenerateCode___closed__10 = _init_l_Lean_Compiler_shouldGenerateCode___closed__10();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__10);
l_Lean_Compiler_shouldGenerateCode___closed__11 = _init_l_Lean_Compiler_shouldGenerateCode___closed__11();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__11);
l_Lean_Compiler_shouldGenerateCode___closed__12 = _init_l_Lean_Compiler_shouldGenerateCode___closed__12();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__12);
l_Lean_Compiler_shouldGenerateCode___closed__13 = _init_l_Lean_Compiler_shouldGenerateCode___closed__13();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__13);
l_Lean_Compiler_shouldGenerateCode___closed__14 = _init_l_Lean_Compiler_shouldGenerateCode___closed__14();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__14);
l_Lean_Compiler_shouldGenerateCode___closed__15 = _init_l_Lean_Compiler_shouldGenerateCode___closed__15();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__15);
l_Lean_Compiler_shouldGenerateCode___closed__16 = _init_l_Lean_Compiler_shouldGenerateCode___closed__16();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__16);
l_Lean_Compiler_shouldGenerateCode___closed__17 = _init_l_Lean_Compiler_shouldGenerateCode___closed__17();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__17);
l_Lean_Compiler_shouldGenerateCode___closed__18 = _init_l_Lean_Compiler_shouldGenerateCode___closed__18();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__18);
l_Lean_Compiler_shouldGenerateCode___closed__19 = _init_l_Lean_Compiler_shouldGenerateCode___closed__19();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__19);
l_Lean_Compiler_shouldGenerateCode___closed__20 = _init_l_Lean_Compiler_shouldGenerateCode___closed__20();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__20);
l_Lean_Compiler_shouldGenerateCode___closed__21 = _init_l_Lean_Compiler_shouldGenerateCode___closed__21();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__21);
l_Lean_Compiler_shouldGenerateCode___closed__22 = _init_l_Lean_Compiler_shouldGenerateCode___closed__22();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__22);
l_Lean_Compiler_shouldGenerateCode___closed__23 = _init_l_Lean_Compiler_shouldGenerateCode___closed__23();
lean_mark_persistent(l_Lean_Compiler_shouldGenerateCode___closed__23);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_checkpoint___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__12);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__13 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__13();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__13);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__14 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__14();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__14);
l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__15 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__15();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_checkpoint___spec__3___closed__15);
l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_compileStage1Impl___spec__4___closed__1);
l_Lean_Compiler_compileStage1Impl___lambda__1___closed__1 = _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_compileStage1Impl___lambda__1___closed__1);
l_Lean_Compiler_compileStage1Impl___lambda__1___closed__2 = _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_compileStage1Impl___lambda__1___closed__2);
l_Lean_Compiler_compileStage1Impl___lambda__1___closed__3 = _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_compileStage1Impl___lambda__1___closed__3);
l_Lean_Compiler_compileStage1Impl___lambda__1___closed__4 = _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_compileStage1Impl___lambda__1___closed__4);
l_Lean_Compiler_compileStage1Impl___lambda__1___closed__5 = _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Compiler_compileStage1Impl___lambda__1___closed__5);
l_Lean_Compiler_compileStage1Impl___lambda__1___closed__6 = _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Compiler_compileStage1Impl___lambda__1___closed__6);
l_Lean_Compiler_compileStage1Impl___lambda__1___closed__7 = _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Compiler_compileStage1Impl___lambda__1___closed__7);
l_Lean_Compiler_compileStage1Impl___lambda__1___closed__8 = _init_l_Lean_Compiler_compileStage1Impl___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Compiler_compileStage1Impl___lambda__1___closed__8);
l_Lean_Compiler_compile___closed__1 = _init_l_Lean_Compiler_compile___closed__1();
lean_mark_persistent(l_Lean_Compiler_compile___closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__1 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__1();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__1);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__2 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__2();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__2);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__3 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__3();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__3);
l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__4 = _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__4();
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728____closed__4);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Main___hyg_728_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
