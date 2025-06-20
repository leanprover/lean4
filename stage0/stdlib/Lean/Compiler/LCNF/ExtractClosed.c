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
static lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
lean_object* l_Array_reverse___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
static lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__12;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__9;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1;
uint8_t l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_markRecDecls_visit_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__14;
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_get_closed_term_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
static lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__0;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
lean_object* lean_cache_closed_term_name(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toExpr(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__1;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
static lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__0;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__13;
static lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__0;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__11;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
uint8_t l_Lean_hasNeverExtractAttribute_visit(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8;
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_box(0);
x_14 = lean_nat_dec_lt(x_11, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_12, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(x_10, x_18, x_19, x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
}
case 4:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(x_21, x_2, x_3, x_4, x_5, x_6, x_7);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get_size(x_22);
x_29 = lean_box(0);
x_30 = lean_nat_dec_lt(x_27, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_28, x_28);
if (x_31 == 0)
{
lean_dec(x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
lean_free_object(x_23);
x_32 = 0;
x_33 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_34 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(x_22, x_32, x_33, x_29, x_2, x_3, x_4, x_5, x_6, x_25);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_22);
x_38 = lean_box(0);
x_39 = lean_nat_dec_lt(x_36, x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_37, x_37);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_45 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(x_22, x_43, x_44, x_38, x_2, x_3, x_4, x_5, x_6, x_35);
return x_45;
}
}
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_7);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(x_1, x_4, x_7);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_13 = lean_box(1);
x_21 = lean_array_uget(x_2, x_3);
lean_inc(x_5);
x_22 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_14 = x_1;
x_15 = x_29;
goto block_20;
}
block_20:
{
if (x_14 == 0)
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_11 = x_15;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_11);
return x_31;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_14; uint8_t x_15; 
x_7 = lean_box(1);
x_14 = lean_array_uget(x_3, x_4);
x_15 = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
x_8 = x_1;
goto block_13;
}
else
{
x_8 = x_2;
goto block_13;
}
block_13:
{
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = lean_unbox(x_7);
return x_12;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_box(1);
x_20 = lean_array_uget(x_1, x_2);
lean_inc(x_4);
x_21 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_12);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_13 = x_11;
x_14 = x_28;
goto block_19;
}
block_19:
{
if (x_13 == 0)
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_10 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0() {
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
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
switch (lean_obj_tag(x_18)) {
case 0:
{
if (x_1 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_18);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0;
x_23 = lean_nat_dec_le(x_22, x_21);
lean_dec(x_21);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
}
case 1:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
default: 
{
lean_dec(x_18);
if (x_1 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
}
}
case 1:
{
lean_dec(x_3);
if (x_1 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
lean_dec(x_2);
x_37 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_36);
return x_37;
}
case 3:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_58; uint8_t x_59; lean_object* x_63; uint8_t x_64; uint8_t x_65; uint8_t x_69; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
lean_dec(x_2);
x_116 = lean_ctor_get(x_3, 1);
lean_inc(x_116);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_array_get_size(x_116);
x_119 = lean_nat_dec_lt(x_117, x_118);
if (x_119 == 0)
{
lean_dec(x_118);
lean_dec(x_116);
x_69 = x_119;
goto block_115;
}
else
{
if (x_119 == 0)
{
lean_dec(x_118);
lean_dec(x_116);
x_69 = x_119;
goto block_115;
}
else
{
size_t x_120; size_t x_121; uint8_t x_122; 
x_120 = 0;
x_121 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_122 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_markRecDecls_visit_spec__0(x_38, x_116, x_120, x_121);
lean_dec(x_116);
if (x_122 == 0)
{
x_69 = x_122;
goto block_115;
}
else
{
uint8_t x_123; 
lean_dec(x_39);
lean_dec(x_38);
x_123 = !lean_is_exclusive(x_3);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_3, 1);
lean_dec(x_124);
x_125 = lean_ctor_get(x_3, 0);
lean_dec(x_125);
x_126 = lean_box(0);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_126);
return x_3;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_3);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_9);
return x_128;
}
}
}
}
block_57:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_array_get_size(x_39);
x_50 = lean_nat_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_39);
x_10 = x_40;
x_11 = x_40;
x_12 = x_47;
goto block_17;
}
else
{
if (x_50 == 0)
{
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_39);
x_10 = x_40;
x_11 = x_40;
x_12 = x_47;
goto block_17;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_53 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0(x_40, x_39, x_51, x_52, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
lean_dec(x_39);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_10 = x_40;
x_11 = x_56;
x_12 = x_55;
goto block_17;
}
}
}
block_62:
{
if (x_59 == 0)
{
x_40 = x_59;
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_58;
goto block_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_39);
lean_dec(x_3);
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
block_68:
{
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_39);
lean_dec(x_3);
x_66 = lean_box(x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
else
{
x_58 = x_63;
x_59 = x_64;
goto block_62;
}
}
block_115:
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_st_ref_get(x_8, x_9);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_38);
x_75 = l_Lean_hasNeverExtractAttribute_visit(x_74, x_38);
if (x_75 == 0)
{
lean_free_object(x_70);
if (x_1 == 0)
{
lean_dec(x_38);
x_40 = x_75;
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_73;
goto block_57;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_st_ref_get(x_8, x_73);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Environment_find_x3f(x_79, x_38, x_75);
if (lean_obj_tag(x_80) == 0)
{
x_40 = x_75;
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_78;
goto block_57;
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
switch (lean_obj_tag(x_81)) {
case 1:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_83, 2);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Expr_isForall(x_84);
lean_dec(x_84);
x_63 = x_78;
x_64 = x_75;
x_65 = x_85;
goto block_68;
}
case 6:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_81);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_array_get_size(x_39);
x_88 = lean_nat_dec_lt(x_86, x_87);
if (x_88 == 0)
{
lean_dec(x_87);
x_63 = x_78;
x_64 = x_75;
x_65 = x_75;
goto block_68;
}
else
{
if (x_88 == 0)
{
lean_dec(x_87);
x_63 = x_78;
x_64 = x_75;
x_65 = x_75;
goto block_68;
}
else
{
size_t x_89; size_t x_90; uint8_t x_91; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_91 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(x_1, x_75, x_39, x_89, x_90);
if (x_91 == 0)
{
x_63 = x_78;
x_64 = x_75;
x_65 = x_75;
goto block_68;
}
else
{
x_63 = x_78;
x_64 = x_75;
x_65 = x_91;
goto block_68;
}
}
}
}
default: 
{
lean_dec(x_81);
x_58 = x_78;
x_59 = x_75;
goto block_62;
}
}
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_3);
x_92 = lean_box(x_69);
lean_ctor_set(x_70, 0, x_92);
return x_70;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_70, 0);
x_94 = lean_ctor_get(x_70, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_70);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_38);
x_96 = l_Lean_hasNeverExtractAttribute_visit(x_95, x_38);
if (x_96 == 0)
{
if (x_1 == 0)
{
lean_dec(x_38);
x_40 = x_96;
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_94;
goto block_57;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_st_ref_get(x_8, x_94);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_Environment_find_x3f(x_100, x_38, x_96);
if (lean_obj_tag(x_101) == 0)
{
x_40 = x_96;
x_41 = x_3;
x_42 = x_4;
x_43 = x_5;
x_44 = x_6;
x_45 = x_7;
x_46 = x_8;
x_47 = x_99;
goto block_57;
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
switch (lean_obj_tag(x_102)) {
case 1:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_104, 2);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lean_Expr_isForall(x_105);
lean_dec(x_105);
x_63 = x_99;
x_64 = x_96;
x_65 = x_106;
goto block_68;
}
case 6:
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_102);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_array_get_size(x_39);
x_109 = lean_nat_dec_lt(x_107, x_108);
if (x_109 == 0)
{
lean_dec(x_108);
x_63 = x_99;
x_64 = x_96;
x_65 = x_96;
goto block_68;
}
else
{
if (x_109 == 0)
{
lean_dec(x_108);
x_63 = x_99;
x_64 = x_96;
x_65 = x_96;
goto block_68;
}
else
{
size_t x_110; size_t x_111; uint8_t x_112; 
x_110 = 0;
x_111 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_112 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(x_1, x_96, x_39, x_110, x_111);
if (x_112 == 0)
{
x_63 = x_99;
x_64 = x_96;
x_65 = x_96;
goto block_68;
}
else
{
x_63 = x_99;
x_64 = x_96;
x_65 = x_112;
goto block_68;
}
}
}
}
default: 
{
lean_dec(x_102);
x_58 = x_99;
x_59 = x_96;
goto block_62;
}
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_3);
x_113 = lean_box(x_69);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_94);
return x_114;
}
}
}
}
default: 
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_129 = lean_ctor_get(x_2, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
lean_dec(x_2);
lean_inc(x_3);
x_131 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(x_129, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_129);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_141 = lean_unsigned_to_nat(0u);
x_142 = lean_array_get_size(x_130);
x_143 = lean_nat_dec_lt(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_142);
lean_dec(x_130);
x_144 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(x_143, x_3, x_4, x_5, x_6, x_7, x_8, x_133);
lean_dec(x_3);
x_134 = x_144;
goto block_140;
}
else
{
if (x_143 == 0)
{
lean_object* x_145; 
lean_dec(x_142);
lean_dec(x_130);
x_145 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(x_143, x_3, x_4, x_5, x_6, x_7, x_8, x_133);
lean_dec(x_3);
x_134 = x_145;
goto block_140;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_146 = 0;
x_147 = lean_usize_of_nat(x_142);
lean_dec(x_142);
lean_inc(x_3);
x_148 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(x_130, x_146, x_147, x_3, x_4, x_5, x_6, x_7, x_8, x_133);
lean_dec(x_130);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_152 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(x_151, x_3, x_4, x_5, x_6, x_7, x_8, x_150);
lean_dec(x_3);
x_134 = x_152;
goto block_140;
}
}
block_140:
{
uint8_t x_135; 
x_135 = lean_unbox(x_132);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_132);
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
else
{
lean_dec(x_132);
return x_134;
}
}
}
}
block_17:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(x_1, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_17, 3);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(x_21, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
return x_22;
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
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(x_6, x_7, x_3, x_8, x_9);
lean_dec(x_3);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
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
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_14);
x_2 = x_19;
x_3 = x_20;
x_9 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 5);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__2;
lean_ctor_set(x_5, 5, x_10);
lean_ctor_set(x_5, 0, x_1);
x_11 = lean_st_ref_set(x_2, x_5, x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 6);
x_23 = lean_ctor_get(x_5, 7);
x_24 = lean_ctor_get(x_5, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_25 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__2;
x_26 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_22);
lean_ctor_set(x_26, 7, x_23);
lean_ctor_set(x_26, 8, x_24);
x_27 = lean_st_ref_set(x_2, x_26, x_6);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg(x_1, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_13, 2);
lean_inc(x_26);
x_16 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
x_16 = x_27;
goto block_25;
}
block_25:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
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
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(316u);
x_4 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1;
x_5 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_closed", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
x_107 = lean_ctor_get(x_81, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_81, 3);
lean_inc(x_108);
x_109 = lean_box(1);
x_110 = lean_unbox(x_109);
lean_inc(x_2);
lean_inc(x_108);
x_111 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(x_110, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; size_t x_128; size_t x_129; uint8_t x_130; 
lean_dec(x_108);
lean_dec(x_107);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
lean_inc(x_82);
x_115 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_128 = lean_ptr_addr(x_82);
lean_dec(x_82);
x_129 = lean_ptr_addr(x_116);
x_130 = lean_usize_dec_eq(x_128, x_129);
if (x_130 == 0)
{
x_119 = x_130;
goto block_127;
}
else
{
size_t x_131; uint8_t x_132; 
x_131 = lean_ptr_addr(x_81);
x_132 = lean_usize_dec_eq(x_131, x_131);
x_119 = x_132;
goto block_127;
}
block_127:
{
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_1);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_1, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_1, 0);
lean_dec(x_122);
lean_ctor_set(x_1, 1, x_116);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_81);
lean_ctor_set(x_124, 1, x_116);
if (lean_is_scalar(x_118)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_118;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_117);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_116);
lean_dec(x_81);
if (lean_is_scalar(x_118)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_118;
}
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_117);
return x_126;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; size_t x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_133 = lean_ctor_get(x_111, 1);
lean_inc(x_133);
lean_dec(x_111);
x_134 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5;
x_135 = lean_st_mk_ref(x_134, x_133);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(x_108, x_136, x_4, x_5, x_6, x_7, x_137);
lean_dec(x_108);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_st_ref_get(x_136, x_139);
lean_dec(x_136);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__10;
x_144 = lean_st_mk_ref(x_143, x_142);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Array_reverse___redArg(x_141);
lean_inc(x_81);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_81);
x_149 = lean_array_push(x_147, x_148);
x_150 = lean_array_size(x_149);
x_151 = 0;
x_152 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(x_150, x_151, x_149, x_145, x_4, x_5, x_6, x_7, x_146);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_st_ref_get(x_145, x_154);
lean_dec(x_145);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_st_ref_get(x_7, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl;
x_162 = l_Array_back_x21___redArg(x_161, x_153);
x_163 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_162);
lean_dec(x_162);
x_164 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Lean_Compiler_LCNF_attachCodeDecls(x_153, x_164);
lean_dec(x_153);
x_166 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__11;
lean_inc(x_165);
x_167 = l_Lean_Compiler_LCNF_Code_toExpr(x_165, x_166);
lean_inc(x_167);
lean_inc(x_160);
x_168 = lean_get_closed_term_name(x_160, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_169 = lean_st_ref_get(x_3, x_159);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_2, 0);
lean_inc(x_172);
x_173 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__13;
x_174 = lean_array_get_size(x_170);
lean_dec(x_170);
x_175 = lean_name_append_index_after(x_173, x_174);
x_176 = l_Lean_Name_append(x_172, x_175);
lean_inc(x_176);
x_177 = lean_cache_closed_term_name(x_160, x_167, x_176);
x_178 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg(x_177, x_7, x_171);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_165);
x_182 = lean_box(0);
x_183 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__14;
lean_inc(x_176);
x_184 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_184, 0, x_176);
lean_ctor_set(x_184, 1, x_180);
lean_ctor_set(x_184, 2, x_107);
lean_ctor_set(x_184, 3, x_166);
lean_ctor_set(x_184, 4, x_181);
lean_ctor_set(x_184, 5, x_183);
x_185 = lean_unbox(x_182);
lean_ctor_set_uint8(x_184, sizeof(void*)*6, x_185);
x_186 = lean_unbox(x_109);
lean_ctor_set_uint8(x_184, sizeof(void*)*6 + 1, x_186);
lean_inc(x_184);
x_187 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_184, x_7, x_179);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_189 = lean_st_ref_take(x_3, x_188);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_array_push(x_190, x_184);
x_193 = lean_st_ref_set(x_3, x_192, x_191);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_83 = x_176;
x_84 = x_2;
x_85 = x_3;
x_86 = x_4;
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_194;
goto block_106;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_167);
lean_dec(x_160);
lean_dec(x_107);
x_195 = lean_ctor_get(x_168, 0);
lean_inc(x_195);
lean_dec(x_168);
x_196 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_165, x_5, x_159);
lean_dec(x_165);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_83 = x_195;
x_84 = x_2;
x_85 = x_3;
x_86 = x_4;
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_197;
goto block_106;
}
}
block_106:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; size_t x_101; uint8_t x_102; 
x_91 = lean_box(0);
x_92 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
x_93 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_93, 0, x_83);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_92);
lean_inc(x_81);
x_94 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_81, x_93, x_87, x_90);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_82);
x_97 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_82, x_84, x_85, x_86, x_87, x_88, x_89, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ptr_addr(x_82);
lean_dec(x_82);
x_101 = lean_ptr_addr(x_98);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_dec(x_81);
x_9 = x_99;
x_10 = x_95;
x_11 = x_98;
x_12 = x_102;
goto block_16;
}
else
{
size_t x_103; size_t x_104; uint8_t x_105; 
x_103 = lean_ptr_addr(x_81);
lean_dec(x_81);
x_104 = lean_ptr_addr(x_95);
x_105 = lean_usize_dec_eq(x_103, x_104);
x_9 = x_99;
x_10 = x_95;
x_11 = x_98;
x_12 = x_105;
goto block_16;
}
}
}
case 1:
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_1, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_1, 1);
lean_inc(x_199);
x_33 = x_198;
x_34 = x_199;
x_35 = x_2;
x_36 = x_3;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
x_40 = x_7;
x_41 = x_8;
goto block_80;
}
case 2:
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_1, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_1, 1);
lean_inc(x_201);
x_33 = x_200;
x_34 = x_201;
x_35 = x_2;
x_36 = x_3;
x_37 = x_4;
x_38 = x_5;
x_39 = x_6;
x_40 = x_7;
x_41 = x_8;
goto block_80;
}
case 4:
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_1, 0);
lean_inc(x_202);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; size_t x_208; size_t x_209; lean_object* x_210; uint8_t x_211; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = lean_ctor_get(x_202, 1);
x_206 = lean_ctor_get(x_202, 2);
x_207 = lean_ctor_get(x_202, 3);
x_208 = lean_array_size(x_207);
x_209 = 0;
lean_inc(x_207);
x_210 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2(x_208, x_209, x_207, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; size_t x_213; size_t x_214; uint8_t x_215; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ptr_addr(x_207);
lean_dec(x_207);
x_214 = lean_ptr_addr(x_212);
x_215 = lean_usize_dec_eq(x_213, x_214);
if (x_215 == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_1);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_1, 0);
lean_dec(x_217);
lean_ctor_set(x_202, 3, x_212);
lean_ctor_set(x_210, 0, x_1);
return x_210;
}
else
{
lean_object* x_218; 
lean_dec(x_1);
lean_ctor_set(x_202, 3, x_212);
x_218 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_218, 0, x_202);
lean_ctor_set(x_210, 0, x_218);
return x_210;
}
}
else
{
lean_dec(x_212);
lean_free_object(x_202);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_ctor_set(x_210, 0, x_1);
return x_210;
}
}
else
{
lean_object* x_219; lean_object* x_220; size_t x_221; size_t x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_210, 0);
x_220 = lean_ctor_get(x_210, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_210);
x_221 = lean_ptr_addr(x_207);
lean_dec(x_207);
x_222 = lean_ptr_addr(x_219);
x_223 = lean_usize_dec_eq(x_221, x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_224 = x_1;
} else {
 lean_dec_ref(x_1);
 x_224 = lean_box(0);
}
lean_ctor_set(x_202, 3, x_219);
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(4, 1, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_202);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_220);
return x_226;
}
else
{
lean_object* x_227; 
lean_dec(x_219);
lean_free_object(x_202);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_1);
lean_ctor_set(x_227, 1, x_220);
return x_227;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; size_t x_232; size_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; size_t x_238; size_t x_239; uint8_t x_240; 
x_228 = lean_ctor_get(x_202, 0);
x_229 = lean_ctor_get(x_202, 1);
x_230 = lean_ctor_get(x_202, 2);
x_231 = lean_ctor_get(x_202, 3);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_202);
x_232 = lean_array_size(x_231);
x_233 = 0;
lean_inc(x_231);
x_234 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2(x_232, x_233, x_231, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_ptr_addr(x_231);
lean_dec(x_231);
x_239 = lean_ptr_addr(x_235);
x_240 = lean_usize_dec_eq(x_238, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_241 = x_1;
} else {
 lean_dec_ref(x_1);
 x_241 = lean_box(0);
}
x_242 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_242, 0, x_228);
lean_ctor_set(x_242, 1, x_229);
lean_ctor_set(x_242, 2, x_230);
lean_ctor_set(x_242, 3, x_235);
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(4, 1, 0);
} else {
 x_243 = x_241;
}
lean_ctor_set(x_243, 0, x_242);
if (lean_is_scalar(x_237)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_237;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_236);
return x_244;
}
else
{
lean_object* x_245; 
lean_dec(x_235);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
if (lean_is_scalar(x_237)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_237;
}
lean_ctor_set(x_245, 0, x_1);
lean_ctor_set(x_245, 1, x_236);
return x_245;
}
}
}
default: 
{
lean_object* x_246; 
lean_dec(x_2);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_1);
lean_ctor_set(x_246, 1, x_8);
return x_246;
}
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
block_24:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
block_32:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
block_80:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_33, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_33, 4);
lean_inc(x_44);
lean_inc(x_35);
x_45 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_44, x_35, x_36, x_37, x_38, x_39, x_40, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_33, x_43, x_42, x_46, x_38, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_50);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ptr_addr(x_55);
lean_dec(x_55);
x_57 = lean_ptr_addr(x_52);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_dec(x_54);
x_17 = x_53;
x_18 = x_49;
x_19 = x_52;
x_20 = x_58;
goto block_24;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_60 = lean_ptr_addr(x_49);
x_61 = lean_usize_dec_eq(x_59, x_60);
x_17 = x_53;
x_18 = x_49;
x_19 = x_52;
x_20 = x_61;
goto block_24;
}
}
case 2:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_dec(x_51);
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_67 = lean_ptr_addr(x_62);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_dec(x_64);
x_25 = x_63;
x_26 = x_49;
x_27 = x_62;
x_28 = x_68;
goto block_32;
}
else
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_64);
lean_dec(x_64);
x_70 = lean_ptr_addr(x_49);
x_71 = lean_usize_dec_eq(x_69, x_70);
x_25 = x_63;
x_26 = x_49;
x_27 = x_62;
x_28 = x_71;
goto block_32;
}
}
default: 
{
uint8_t x_72; 
lean_dec(x_49);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_51);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_51, 0);
lean_dec(x_73);
x_74 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3;
x_75 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_74);
lean_ctor_set(x_51, 0, x_75);
return x_51;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_51, 1);
lean_inc(x_76);
lean_dec(x_51);
x_77 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3;
x_78 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0() {
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
x_16 = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0;
x_17 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(x_16, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_35 = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0;
x_36 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(x_35, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_13);
lean_inc(x_11);
x_14 = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(x_1, x_9, x_11, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
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
lean_dec(x_11);
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
lean_inc(x_29);
x_33 = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(x_1, x_32, x_29, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_29, x_35);
lean_dec(x_29);
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
x_40 = lean_array_push(x_37, x_34);
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
lean_dec(x_29);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_19 = l_Lean_Compiler_LCNF_Decl_extractClosed(x_18, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_append___redArg(x_5, x_20);
lean_dec(x_20);
x_11 = x_22;
x_12 = x_21;
goto block_16;
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_11 = x_23;
x_12 = x_24;
goto block_16;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_19;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extract_closed", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__1;
x_2 = l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__2;
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_KVMap_getBool(x_8, x_9, x_11);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_mk_empty_array_with_capacity(x_1);
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_15);
lean_dec(x_15);
lean_inc(x_2);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0(x_2, x_2, x_20, x_21, x_14, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extractClosed", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_extractClosed___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extractClosed() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(1);
x_4 = lean_box(0);
x_5 = l_Lean_Compiler_LCNF_extractClosed___closed__1;
x_6 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_8);
x_9 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 2, x_9);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_extractClosed___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_extractClosed___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ExtractClosed", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1860u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
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
l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0 = _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0);
l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__0 = _init_l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__0);
l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__1 = _init_l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__1);
l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__2 = _init_l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__2);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0);
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
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__9 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__9);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__10 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__10);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__11 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__11);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__12 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__12);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__13 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__13);
l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__14 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__14);
l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0 = _init_l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0);
l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0);
l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__0);
l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__1);
l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__2 = _init_l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___lam__0___closed__2);
l_Lean_Compiler_LCNF_extractClosed___closed__0 = _init_l_Lean_Compiler_LCNF_extractClosed___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___closed__0);
l_Lean_Compiler_LCNF_extractClosed___closed__1 = _init_l_Lean_Compiler_LCNF_extractClosed___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___closed__1);
l_Lean_Compiler_LCNF_extractClosed = _init_l_Lean_Compiler_LCNF_extractClosed();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1860_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
