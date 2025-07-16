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
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extractClosed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__12;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__9;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1;
uint8_t l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_markRecDecls_visit_spec__0(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__14;
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_getClosedTermName_x3f(lean_object*, lean_object*);
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
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_(lean_object*);
static lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* l_Lean_cacheClosedTermName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_toExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCodeDecl;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(uint8_t, uint8_t, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extractClosed___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_hasNeverExtractAttribute_visit(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
static lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__8;
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
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
lean_dec_ref(x_8);
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
lean_dec_ref(x_19);
lean_inc(x_18);
lean_ctor_set_tag(x_9, 0);
x_22 = lean_array_push(x_20, x_9);
x_23 = lean_st_ref_set(x_2, x_22, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec_ref(x_23);
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
lean_dec_ref(x_28);
lean_inc(x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_27);
x_32 = lean_array_push(x_29, x_31);
x_33 = lean_st_ref_set(x_2, x_32, x_30);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = 1;
x_22 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_5);
x_23 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec_ref(x_5);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(x_13);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(x_13);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec_ref(x_23);
x_14 = x_1;
x_15 = x_32;
goto block_21;
}
block_21:
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
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_5);
x_19 = lean_box(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_5);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
return x_35;
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
uint8_t x_7; uint8_t x_8; lean_object* x_13; uint8_t x_14; 
x_7 = 1;
x_13 = lean_array_uget(x_3, x_4);
x_14 = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
x_8 = x_1;
goto block_12;
}
else
{
x_8 = x_2;
goto block_12;
}
block_12:
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
return x_7;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
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
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_12 = 1;
x_21 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_4);
x_22 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec_ref(x_4);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(x_12);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(x_12);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec_ref(x_22);
x_13 = x_11;
x_14 = x_31;
goto block_20;
}
block_20:
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
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_4);
x_18 = lean_box(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_4);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
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
lean_object* x_19; 
lean_dec_ref(x_3);
x_19 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_19);
lean_dec(x_2);
switch (lean_obj_tag(x_19)) {
case 0:
{
if (x_1 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec_ref(x_19);
x_24 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0;
x_25 = lean_nat_dec_le(x_24, x_23);
lean_dec(x_23);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
case 1:
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_19);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
default: 
{
lean_dec_ref(x_19);
if (x_1 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
}
}
}
case 1:
{
lean_dec_ref(x_3);
if (x_1 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_9);
return x_42;
}
}
case 2:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
lean_dec(x_2);
x_44 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_43);
return x_44;
}
case 3:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_65; lean_object* x_66; uint8_t x_70; lean_object* x_71; uint8_t x_72; uint8_t x_76; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_46);
lean_dec(x_2);
x_123 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_123);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_array_get_size(x_123);
x_126 = lean_nat_dec_lt(x_124, x_125);
if (x_126 == 0)
{
lean_dec(x_125);
lean_dec_ref(x_123);
x_76 = x_126;
goto block_122;
}
else
{
if (x_126 == 0)
{
lean_dec(x_125);
lean_dec_ref(x_123);
x_76 = x_126;
goto block_122;
}
else
{
size_t x_127; size_t x_128; uint8_t x_129; 
x_127 = 0;
x_128 = lean_usize_of_nat(x_125);
lean_dec(x_125);
x_129 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_markRecDecls_visit_spec__0(x_45, x_123, x_127, x_128);
lean_dec_ref(x_123);
if (x_129 == 0)
{
x_76 = x_129;
goto block_122;
}
else
{
uint8_t x_130; 
lean_dec_ref(x_46);
lean_dec(x_45);
x_130 = !lean_is_exclusive(x_3);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_3, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_3, 0);
lean_dec(x_132);
x_133 = 0;
x_134 = lean_box(x_133);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_134);
return x_3;
}
else
{
uint8_t x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_3);
x_135 = 0;
x_136 = lean_box(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_9);
return x_137;
}
}
}
}
block_64:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_46);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
lean_dec(x_56);
lean_dec_ref(x_48);
lean_dec_ref(x_46);
x_10 = x_47;
x_11 = x_47;
x_12 = x_54;
goto block_18;
}
else
{
if (x_57 == 0)
{
lean_dec(x_56);
lean_dec_ref(x_48);
lean_dec_ref(x_46);
x_10 = x_47;
x_11 = x_47;
x_12 = x_54;
goto block_18;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_60 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0(x_47, x_46, x_58, x_59, x_48, x_49, x_50, x_51, x_52, x_53, x_54);
lean_dec_ref(x_46);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
x_10 = x_47;
x_11 = x_63;
x_12 = x_62;
goto block_18;
}
}
}
block_69:
{
if (x_65 == 0)
{
x_47 = x_65;
x_48 = x_3;
x_49 = x_4;
x_50 = x_5;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_66;
goto block_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_46);
lean_dec_ref(x_3);
x_67 = lean_box(x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
block_75:
{
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_46);
lean_dec_ref(x_3);
x_73 = lean_box(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
x_65 = x_70;
x_66 = x_71;
goto block_69;
}
}
block_122:
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_st_ref_get(x_8, x_9);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = lean_ctor_get(x_79, 0);
lean_inc_ref(x_81);
lean_dec(x_79);
lean_inc(x_45);
x_82 = l_Lean_hasNeverExtractAttribute_visit(x_81, x_45);
if (x_82 == 0)
{
lean_free_object(x_77);
if (x_1 == 0)
{
lean_dec(x_45);
x_47 = x_82;
x_48 = x_3;
x_49 = x_4;
x_50 = x_5;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_80;
goto block_64;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_st_ref_get(x_8, x_80);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_86);
lean_dec(x_84);
x_87 = l_Lean_Environment_find_x3f(x_86, x_45, x_82);
if (lean_obj_tag(x_87) == 0)
{
x_47 = x_82;
x_48 = x_3;
x_49 = x_4;
x_50 = x_5;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_85;
goto block_64;
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec(x_87);
switch (lean_obj_tag(x_88)) {
case 1:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_90);
lean_dec_ref(x_89);
x_91 = lean_ctor_get(x_90, 2);
lean_inc_ref(x_91);
lean_dec_ref(x_90);
x_92 = l_Lean_Expr_isForall(x_91);
lean_dec_ref(x_91);
x_70 = x_82;
x_71 = x_85;
x_72 = x_92;
goto block_75;
}
case 6:
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_88);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_array_get_size(x_46);
x_95 = lean_nat_dec_lt(x_93, x_94);
if (x_95 == 0)
{
lean_dec(x_94);
x_70 = x_82;
x_71 = x_85;
x_72 = x_82;
goto block_75;
}
else
{
if (x_95 == 0)
{
lean_dec(x_94);
x_70 = x_82;
x_71 = x_85;
x_72 = x_82;
goto block_75;
}
else
{
size_t x_96; size_t x_97; uint8_t x_98; 
x_96 = 0;
x_97 = lean_usize_of_nat(x_94);
lean_dec(x_94);
x_98 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(x_1, x_82, x_46, x_96, x_97);
if (x_98 == 0)
{
x_70 = x_82;
x_71 = x_85;
x_72 = x_82;
goto block_75;
}
else
{
x_70 = x_82;
x_71 = x_85;
x_72 = x_98;
goto block_75;
}
}
}
}
default: 
{
lean_dec(x_88);
x_65 = x_82;
x_66 = x_85;
goto block_69;
}
}
}
}
}
else
{
lean_object* x_99; 
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_3);
x_99 = lean_box(x_76);
lean_ctor_set(x_77, 0, x_99);
return x_77;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_77, 0);
x_101 = lean_ctor_get(x_77, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_77);
x_102 = lean_ctor_get(x_100, 0);
lean_inc_ref(x_102);
lean_dec(x_100);
lean_inc(x_45);
x_103 = l_Lean_hasNeverExtractAttribute_visit(x_102, x_45);
if (x_103 == 0)
{
if (x_1 == 0)
{
lean_dec(x_45);
x_47 = x_103;
x_48 = x_3;
x_49 = x_4;
x_50 = x_5;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_101;
goto block_64;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_st_ref_get(x_8, x_101);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_107);
lean_dec(x_105);
x_108 = l_Lean_Environment_find_x3f(x_107, x_45, x_103);
if (lean_obj_tag(x_108) == 0)
{
x_47 = x_103;
x_48 = x_3;
x_49 = x_4;
x_50 = x_5;
x_51 = x_6;
x_52 = x_7;
x_53 = x_8;
x_54 = x_106;
goto block_64;
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
switch (lean_obj_tag(x_109)) {
case 1:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc_ref(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc_ref(x_111);
lean_dec_ref(x_110);
x_112 = lean_ctor_get(x_111, 2);
lean_inc_ref(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_Expr_isForall(x_112);
lean_dec_ref(x_112);
x_70 = x_103;
x_71 = x_106;
x_72 = x_113;
goto block_75;
}
case 6:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_109);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_array_get_size(x_46);
x_116 = lean_nat_dec_lt(x_114, x_115);
if (x_116 == 0)
{
lean_dec(x_115);
x_70 = x_103;
x_71 = x_106;
x_72 = x_103;
goto block_75;
}
else
{
if (x_116 == 0)
{
lean_dec(x_115);
x_70 = x_103;
x_71 = x_106;
x_72 = x_103;
goto block_75;
}
else
{
size_t x_117; size_t x_118; uint8_t x_119; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_119 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(x_1, x_103, x_46, x_117, x_118);
if (x_119 == 0)
{
x_70 = x_103;
x_71 = x_106;
x_72 = x_103;
goto block_75;
}
else
{
x_70 = x_103;
x_71 = x_106;
x_72 = x_119;
goto block_75;
}
}
}
}
default: 
{
lean_dec(x_109);
x_65 = x_103;
x_66 = x_106;
goto block_69;
}
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_3);
x_120 = lean_box(x_76);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_101);
return x_121;
}
}
}
}
default: 
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_138 = lean_ctor_get(x_2, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_139);
lean_dec(x_2);
lean_inc_ref(x_3);
x_140 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(x_138, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_138);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec_ref(x_140);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_array_get_size(x_139);
x_152 = lean_nat_dec_lt(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; 
lean_dec(x_151);
lean_dec_ref(x_139);
x_153 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
lean_dec_ref(x_3);
x_143 = x_153;
goto block_149;
}
else
{
if (x_152 == 0)
{
lean_object* x_154; 
lean_dec(x_151);
lean_dec_ref(x_139);
x_154 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
lean_dec_ref(x_3);
x_143 = x_154;
goto block_149;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; 
x_155 = 0;
x_156 = lean_usize_of_nat(x_151);
lean_dec(x_151);
lean_inc_ref(x_3);
x_157 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(x_139, x_155, x_156, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
lean_dec_ref(x_139);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_160 = lean_unbox(x_158);
lean_dec(x_158);
x_161 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(x_160, x_3, x_4, x_5, x_6, x_7, x_8, x_159);
lean_dec_ref(x_3);
x_143 = x_161;
goto block_149;
}
}
block_149:
{
uint8_t x_144; 
x_144 = lean_unbox(x_141);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
lean_ctor_set(x_143, 0, x_141);
return x_143;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
lean_dec(x_141);
return x_143;
}
}
}
}
block_18:
{
if (x_11 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
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
lean_dec_ref(x_2);
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
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec_ref(x_9);
x_21 = lean_ctor_get(x_19, 3);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
x_23 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(x_22, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
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
lean_dec_ref(x_2);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__0(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(x_6, x_7, x_3, x_8, x_9);
lean_dec_ref(x_3);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(0u);
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
lean_dec_ref(x_4);
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
lean_dec_ref(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_26);
x_16 = x_26;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_27);
x_16 = x_27;
goto block_25;
}
block_25:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
lean_inc_ref(x_4);
x_17 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
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
x_3 = lean_unsigned_to_nat(315u);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_82);
x_107 = lean_ctor_get(x_81, 2);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_81, 3);
lean_inc(x_108);
x_109 = 1;
lean_inc_ref(x_2);
lean_inc(x_108);
x_110 = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(x_109, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; size_t x_127; size_t x_128; uint8_t x_129; 
lean_dec(x_108);
lean_dec_ref(x_107);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec_ref(x_110);
lean_inc_ref(x_82);
x_114 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_127 = lean_ptr_addr(x_82);
lean_dec_ref(x_82);
x_128 = lean_ptr_addr(x_115);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
x_118 = x_129;
goto block_126;
}
else
{
size_t x_130; uint8_t x_131; 
x_130 = lean_ptr_addr(x_81);
x_131 = lean_usize_dec_eq(x_130, x_130);
x_118 = x_131;
goto block_126;
}
block_126:
{
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_1);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_1, 1);
lean_dec(x_120);
x_121 = lean_ctor_get(x_1, 0);
lean_dec(x_121);
lean_ctor_set(x_1, 1, x_115);
if (lean_is_scalar(x_117)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_117;
}
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_116);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_1);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_81);
lean_ctor_set(x_123, 1, x_115);
if (lean_is_scalar(x_117)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_117;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_116);
return x_124;
}
}
else
{
lean_object* x_125; 
lean_dec(x_115);
lean_dec_ref(x_81);
if (lean_is_scalar(x_117)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_117;
}
lean_ctor_set(x_125, 0, x_1);
lean_ctor_set(x_125, 1, x_116);
return x_125;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; size_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_132 = lean_ctor_get(x_110, 1);
lean_inc(x_132);
lean_dec_ref(x_110);
x_133 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__5;
x_134 = lean_st_mk_ref(x_133, x_132);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec_ref(x_134);
x_137 = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(x_108, x_135, x_4, x_5, x_6, x_7, x_136);
lean_dec(x_108);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = lean_st_ref_get(x_135, x_138);
lean_dec(x_135);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec_ref(x_139);
x_142 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__10;
x_143 = lean_st_mk_ref(x_142, x_141);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
x_146 = l_Array_reverse___redArg(x_140);
lean_inc_ref(x_81);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_81);
x_148 = lean_array_push(x_146, x_147);
x_149 = lean_array_size(x_148);
x_150 = 0;
x_151 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(x_149, x_150, x_148, x_144, x_4, x_5, x_6, x_7, x_145);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec_ref(x_151);
x_154 = lean_st_ref_get(x_144, x_153);
lean_dec(x_144);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec_ref(x_154);
x_156 = lean_st_ref_get(x_7, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc_ref(x_159);
lean_dec(x_157);
x_160 = l_Lean_Compiler_LCNF_instInhabitedCodeDecl;
x_161 = l_Array_back_x21___redArg(x_160, x_152);
x_162 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l_Lean_Compiler_LCNF_attachCodeDecls(x_152, x_163);
lean_dec(x_152);
x_165 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__11;
lean_inc_ref(x_164);
x_166 = l_Lean_Compiler_LCNF_Code_toExpr(x_164, x_165);
lean_inc_ref(x_166);
lean_inc_ref(x_159);
x_167 = l_Lean_getClosedTermName_x3f(x_159, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_168 = lean_st_ref_get(x_3, x_158);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec_ref(x_168);
x_171 = lean_ctor_get(x_2, 0);
lean_inc(x_171);
x_172 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__13;
x_173 = lean_array_get_size(x_169);
lean_dec(x_169);
x_174 = lean_name_append_index_after(x_172, x_173);
x_175 = l_Lean_Name_append(x_171, x_174);
lean_inc(x_175);
x_176 = l_Lean_cacheClosedTermName(x_159, x_166, x_175);
x_177 = l_Lean_setEnv___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___redArg(x_176, x_7, x_170);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_164);
x_181 = 0;
x_182 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__14;
lean_inc(x_175);
x_183 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_183, 0, x_175);
lean_ctor_set(x_183, 1, x_179);
lean_ctor_set(x_183, 2, x_107);
lean_ctor_set(x_183, 3, x_165);
lean_ctor_set(x_183, 4, x_180);
lean_ctor_set(x_183, 5, x_182);
lean_ctor_set_uint8(x_183, sizeof(void*)*6, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*6 + 1, x_109);
lean_inc_ref(x_183);
x_184 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_183, x_7, x_178);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = lean_st_ref_take(x_3, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec_ref(x_186);
x_189 = lean_array_push(x_187, x_183);
x_190 = lean_st_ref_set(x_3, x_189, x_188);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec_ref(x_190);
x_83 = x_175;
x_84 = x_2;
x_85 = x_3;
x_86 = x_4;
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_191;
goto block_106;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_166);
lean_dec_ref(x_159);
lean_dec_ref(x_107);
x_192 = lean_ctor_get(x_167, 0);
lean_inc(x_192);
lean_dec(x_167);
x_193 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_164, x_5, x_158);
lean_dec_ref(x_164);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec_ref(x_193);
x_83 = x_192;
x_84 = x_2;
x_85 = x_3;
x_86 = x_4;
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_194;
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
lean_inc_ref(x_81);
x_94 = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(x_81, x_93, x_87, x_90);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
lean_inc_ref(x_82);
x_97 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_82, x_84, x_85, x_86, x_87, x_88, x_89, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_ptr_addr(x_82);
lean_dec_ref(x_82);
x_101 = lean_ptr_addr(x_98);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_dec_ref(x_81);
x_9 = x_99;
x_10 = x_98;
x_11 = x_95;
x_12 = x_102;
goto block_16;
}
else
{
size_t x_103; size_t x_104; uint8_t x_105; 
x_103 = lean_ptr_addr(x_81);
lean_dec_ref(x_81);
x_104 = lean_ptr_addr(x_95);
x_105 = lean_usize_dec_eq(x_103, x_104);
x_9 = x_99;
x_10 = x_98;
x_11 = x_95;
x_12 = x_105;
goto block_16;
}
}
}
case 1:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_196);
x_33 = x_195;
x_34 = x_196;
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
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_198);
x_33 = x_197;
x_34 = x_198;
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
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_199);
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
lean_inc_ref(x_204);
x_207 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2(x_205, x_206, x_204, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; size_t x_210; size_t x_211; uint8_t x_212; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ptr_addr(x_204);
lean_dec_ref(x_204);
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
lean_dec_ref(x_202);
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
lean_dec_ref(x_204);
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
lean_dec_ref(x_202);
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
lean_inc_ref(x_228);
x_231 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__2(x_229, x_230, x_228, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_dec_ref(x_228);
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
lean_dec_ref(x_226);
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
lean_dec_ref(x_2);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_1);
lean_ctor_set(x_243, 1, x_8);
return x_243;
}
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
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
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
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
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
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
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_33, 3);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_33, 4);
lean_inc_ref(x_44);
lean_inc_ref(x_35);
x_45 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_44, x_35, x_36, x_37, x_38, x_39, x_40, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_33, x_43, x_42, x_46, x_38, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_50);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_55);
x_56 = lean_ptr_addr(x_55);
lean_dec_ref(x_55);
x_57 = lean_ptr_addr(x_52);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_dec_ref(x_54);
x_17 = x_53;
x_18 = x_52;
x_19 = x_49;
x_20 = x_58;
goto block_24;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_54);
lean_dec_ref(x_54);
x_60 = lean_ptr_addr(x_49);
x_61 = lean_usize_dec_eq(x_59, x_60);
x_17 = x_53;
x_18 = x_52;
x_19 = x_49;
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
lean_dec_ref(x_51);
x_64 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_65);
x_66 = lean_ptr_addr(x_65);
lean_dec_ref(x_65);
x_67 = lean_ptr_addr(x_62);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_dec_ref(x_64);
x_25 = x_63;
x_26 = x_62;
x_27 = x_49;
x_28 = x_68;
goto block_32;
}
else
{
size_t x_69; size_t x_70; uint8_t x_71; 
x_69 = lean_ptr_addr(x_64);
lean_dec_ref(x_64);
x_70 = lean_ptr_addr(x_49);
x_71 = lean_usize_dec_eq(x_69, x_70);
x_25 = x_63;
x_26 = x_62;
x_27 = x_49;
x_28 = x_71;
goto block_32;
}
}
default: 
{
uint8_t x_72; 
lean_dec(x_49);
lean_dec_ref(x_1);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_13);
lean_dec_ref(x_12);
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
lean_dec_ref(x_30);
lean_dec_ref(x_29);
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
lean_dec_ref(x_14);
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
lean_dec_ref(x_33);
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
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_19 = l_Lean_Compiler_LCNF_Decl_extractClosed(x_18, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Array_append___redArg(x_5, x_20);
lean_dec(x_20);
x_11 = x_22;
x_12 = x_21;
goto block_16;
}
else
{
lean_dec_ref(x_5);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec_ref(x_19);
x_11 = x_23;
x_12 = x_24;
goto block_16;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_19;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extractClosed___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Compiler_LCNF_getConfig___redArg(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_mk_empty_array_with_capacity(x_1);
x_19 = lean_array_get_size(x_2);
x_20 = lean_nat_dec_lt(x_1, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
lean_free_object(x_8);
x_22 = 0;
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
lean_inc_ref(x_2);
x_24 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0(x_2, x_2, x_22, x_23, x_18, x_3, x_4, x_5, x_6, x_16);
lean_dec_ref(x_2);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_mk_empty_array_with_capacity(x_1);
x_27 = lean_array_get_size(x_2);
x_28 = lean_nat_dec_lt(x_1, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_27);
lean_dec(x_27);
lean_inc_ref(x_2);
x_34 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_extractClosed_spec__0(x_2, x_2, x_32, x_33, x_26, x_3, x_4, x_5, x_6, x_25);
lean_dec_ref(x_2);
return x_34;
}
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
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = 1;
x_4 = 0;
x_5 = l_Lean_Compiler_LCNF_extractClosed___closed__1;
x_6 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 2, x_4);
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
lean_dec_ref(x_2);
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_extractClosed___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ExtractClosed", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1859u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_;
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
l_Lean_Compiler_LCNF_extractClosed___closed__0 = _init_l_Lean_Compiler_LCNF_extractClosed___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___closed__0);
l_Lean_Compiler_LCNF_extractClosed___closed__1 = _init_l_Lean_Compiler_LCNF_extractClosed___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed___closed__1);
l_Lean_Compiler_LCNF_extractClosed = _init_l_Lean_Compiler_LCNF_extractClosed();
lean_mark_persistent(l_Lean_Compiler_LCNF_extractClosed);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ExtractClosed___hyg_1859_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
