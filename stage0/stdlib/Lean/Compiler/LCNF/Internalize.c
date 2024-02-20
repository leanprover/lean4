// Lean compiler output
// Module: Lean.Compiler.LCNF.Internalize
// Imports: Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.CompilerM
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
lean_object* l_Lean_Compiler_LCNF_normArg___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__2;
lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_cleanup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM;
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_cleanup___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__1;
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_modify___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cleanup___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_cleanup___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normArg___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_modify___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_cleanup___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_cleanup___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_st_ref_get(x_3, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Name_num___override(x_7, x_11);
x_13 = lean_st_ref_take(x_3, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_st_ref_set(x_3, x_20, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_12);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_6);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___spec__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_StateRefT_x27_get___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_modify___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_1(x_1, x_9);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_modify___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___spec__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_modify___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_modify___at_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Name_num___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
x_27 = lean_ctor_get(x_14, 5);
x_28 = lean_ctor_get(x_14, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_28);
x_30 = lean_st_ref_set(x_1, x_29, x_15);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
lean_inc(x_35);
lean_inc(x_34);
x_36 = l_Lean_Name_num___override(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_35, x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_st_ref_take(x_1, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 7, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set(x_50, 6, x_48);
x_51 = lean_st_ref_set(x_1, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___rarg___boxed), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___rarg(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = l_Lean_mkFreshFVarId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l_Lean_Expr_fvar___override(x_9);
x_15 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_12, x_1, x_14);
x_16 = lean_st_ref_set(x_2, x_15, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_9);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkFreshId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(x_10, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_16, x_18, x_11);
x_20 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_9, x_2, x_3, x_4, x_5, x_6, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_1, 2, x_19);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_21);
x_23 = lean_st_ref_take(x_4, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_1);
x_28 = l_Lean_Compiler_LCNF_LCtx_addParam(x_27, x_1);
lean_ctor_set(x_24, 0, x_28);
x_29 = lean_st_ref_set(x_4, x_24, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_1);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
lean_inc(x_1);
x_36 = l_Lean_Compiler_LCNF_LCtx_addParam(x_34, x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_st_ref_set(x_4, x_37, x_25);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_1);
x_46 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(x_43, x_3, x_4, x_5, x_6, x_7);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_get(x_2, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = 1;
x_53 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_50, x_52, x_44);
x_54 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_42, x_2, x_3, x_4, x_5, x_6, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_45);
x_58 = lean_st_ref_take(x_4, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
lean_inc(x_57);
x_64 = l_Lean_Compiler_LCNF_LCtx_addParam(x_61, x_57);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
x_66 = lean_st_ref_set(x_4, x_65, x_60);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_st_ref_get(x_2, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_16, x_12);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_st_ref_get(x_2, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_20, x_18, x_16);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_23, x_2, x_3, x_4, x_5, x_6, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_22);
x_28 = lean_st_ref_take(x_4, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_27);
x_33 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_32, x_27);
lean_ctor_set(x_29, 0, x_33);
x_34 = lean_st_ref_set(x_4, x_29, x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_27);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
lean_inc(x_27);
x_41 = l_Lean_Compiler_LCNF_LCtx_addLetDecl(x_39, x_27);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_st_ref_set(x_4, x_42, x_30);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_2, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_10, x_12, x_8);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_refreshBinderName(x_14, x_3, x_4, x_5, x_6, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_array_get_size(x_18);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_20, x_21, x_18, x_2, x_3, x_4, x_5, x_6, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_1, 4);
lean_inc(x_25);
x_26 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_25, x_2, x_3, x_4, x_5, x_6, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l___private_Lean_Compiler_LCNF_Internalize_0__Lean_Compiler_LCNF_Internalize_mkNewFVarId(x_29, x_2, x_3, x_4, x_5, x_6, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_13);
lean_ctor_set(x_33, 4, x_27);
x_34 = lean_st_ref_take(x_4, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_33);
x_39 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_38, x_33);
lean_ctor_set(x_35, 0, x_39);
x_40 = lean_st_ref_set(x_4, x_35, x_36);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_33);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_35, 0);
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_35);
lean_inc(x_33);
x_47 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_45, x_33);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_st_ref_set(x_4, x_48, x_36);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
lean_object* l_Lean_Compiler_LCNF_normArg___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_11, x_2, x_1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_13, x_2, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = 1;
x_16 = l_Lean_Compiler_LCNF_normArg___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__1(x_15, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_14, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
x_9 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 2);
x_18 = lean_array_get_size(x_16);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_19, x_20, x_16, x_4, x_5, x_6, x_7, x_8, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_17, x_4, x_5, x_6, x_7, x_8, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_ctor_set(x_12, 2, x_25);
lean_ctor_set(x_12, 1, x_22);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_29 = lean_array_uset(x_14, x_2, x_12);
x_2 = x_28;
x_3 = x_29;
x_9 = x_26;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_34 = lean_array_get_size(x_32);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_35, x_36, x_32, x_4, x_5, x_6, x_7, x_8, x_9);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_33, x_4, x_5, x_6, x_7, x_8, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_41);
x_44 = 1;
x_45 = lean_usize_add(x_2, x_44);
x_46 = lean_array_uset(x_14, x_2, x_43);
x_2 = x_45;
x_3 = x_46;
x_9 = x_42;
goto _start;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_12, 0);
x_50 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_49, x_4, x_5, x_6, x_7, x_8, x_9);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_ctor_set(x_12, 0, x_51);
x_53 = 1;
x_54 = lean_usize_add(x_2, x_53);
x_55 = lean_array_uset(x_14, x_2, x_12);
x_2 = x_54;
x_3 = x_55;
x_9 = x_52;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_12, 0);
lean_inc(x_57);
lean_dec(x_12);
x_58 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_57, x_4, x_5, x_6, x_7, x_8, x_9);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
x_62 = 1;
x_63 = lean_usize_add(x_2, x_62);
x_64 = lean_array_uset(x_14, x_2, x_61);
x_2 = x_63;
x_3 = x_64;
x_9 = x_60;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_10, x_2, x_3, x_4, x_5, x_6, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_20, x_2, x_3, x_4, x_5, x_6, x_7);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_21, x_2, x_3, x_4, x_5, x_6, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
case 1:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_32, x_2, x_3, x_4, x_5, x_6, x_7);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_33, x_2, x_3, x_4, x_5, x_6, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_35);
lean_ctor_set(x_37, 0, x_1);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_37);
lean_ctor_set(x_1, 1, x_40);
lean_ctor_set(x_1, 0, x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_1);
x_45 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_43, x_2, x_3, x_4, x_5, x_6, x_7);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_44, x_2, x_3, x_4, x_5, x_6, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_49);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
case 2:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_1);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_1, 1);
x_57 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_55, x_2, x_3, x_4, x_5, x_6, x_7);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_56, x_2, x_3, x_4, x_5, x_6, x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_ctor_set(x_1, 1, x_62);
lean_ctor_set(x_1, 0, x_58);
lean_ctor_set(x_60, 0, x_1);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_60);
lean_ctor_set(x_1, 1, x_63);
lean_ctor_set(x_1, 0, x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_1, 0);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_1);
x_68 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_66, x_2, x_3, x_4, x_5, x_6, x_7);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_67, x_2, x_3, x_4, x_5, x_6, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_72);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
case 3:
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_1);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_ctor_get(x_1, 1);
x_80 = lean_st_ref_get(x_2, x_7);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = 1;
x_84 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_81, x_78, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_array_get_size(x_79);
x_87 = lean_usize_of_nat(x_86);
lean_dec(x_86);
x_88 = 0;
x_89 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__2(x_87, x_88, x_79, x_2, x_3, x_4, x_5, x_6, x_82);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set(x_89, 0, x_1);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_89, 0);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_89);
lean_ctor_set(x_1, 1, x_92);
lean_ctor_set(x_1, 0, x_85);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
lean_object* x_95; 
lean_free_object(x_1);
lean_dec(x_79);
x_95 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_82);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_1, 0);
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_1);
x_98 = lean_st_ref_get(x_2, x_7);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = 1;
x_102 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_99, x_96, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_array_get_size(x_97);
x_105 = lean_usize_of_nat(x_104);
lean_dec(x_104);
x_106 = 0;
x_107 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__2(x_105, x_106, x_97, x_2, x_3, x_4, x_5, x_6, x_100);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_108);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; 
lean_dec(x_97);
x_113 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_100);
return x_113;
}
}
}
case 4:
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_1);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_1, 0);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_115, 2);
x_120 = lean_ctor_get(x_115, 3);
x_121 = lean_st_ref_get(x_2, x_7);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = 1;
x_125 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_122, x_119, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; uint8_t x_135; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_get(x_2, x_123);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_128, x_124, x_118);
x_131 = lean_array_get_size(x_120);
x_132 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_133 = 0;
x_134 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__3(x_132, x_133, x_120, x_2, x_3, x_4, x_5, x_6, x_129);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_134, 0);
lean_ctor_set(x_115, 3, x_136);
lean_ctor_set(x_115, 2, x_126);
lean_ctor_set(x_115, 1, x_130);
lean_ctor_set(x_134, 0, x_1);
return x_134;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_134, 0);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_134);
lean_ctor_set(x_115, 3, x_137);
lean_ctor_set(x_115, 2, x_126);
lean_ctor_set(x_115, 1, x_130);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
else
{
lean_object* x_140; 
lean_free_object(x_115);
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_117);
lean_free_object(x_1);
x_140 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_123);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_115, 0);
x_142 = lean_ctor_get(x_115, 1);
x_143 = lean_ctor_get(x_115, 2);
x_144 = lean_ctor_get(x_115, 3);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_115);
x_145 = lean_st_ref_get(x_2, x_7);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = 1;
x_149 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_146, x_143, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; size_t x_156; size_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_st_ref_get(x_2, x_147);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_152, x_148, x_142);
x_155 = lean_array_get_size(x_144);
x_156 = lean_usize_of_nat(x_155);
lean_dec(x_155);
x_157 = 0;
x_158 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__3(x_156, x_157, x_144, x_2, x_3, x_4, x_5, x_6, x_153);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_141);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_150);
lean_ctor_set(x_162, 3, x_159);
lean_ctor_set(x_1, 0, x_162);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_1);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
else
{
lean_object* x_164; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_free_object(x_1);
x_164 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_147);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_165 = lean_ctor_get(x_1, 0);
lean_inc(x_165);
lean_dec(x_1);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 x_170 = x_165;
} else {
 lean_dec_ref(x_165);
 x_170 = lean_box(0);
}
x_171 = lean_st_ref_get(x_2, x_7);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = 1;
x_175 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_172, x_168, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; size_t x_182; size_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_st_ref_get(x_2, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_178, x_174, x_167);
x_181 = lean_array_get_size(x_169);
x_182 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_183 = 0;
x_184 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__3(x_182, x_183, x_169, x_2, x_3, x_4, x_5, x_6, x_179);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_188 = lean_alloc_ctor(0, 4, 0);
} else {
 x_188 = x_170;
}
lean_ctor_set(x_188, 0, x_166);
lean_ctor_set(x_188, 1, x_180);
lean_ctor_set(x_188, 2, x_176);
lean_ctor_set(x_188, 3, x_185);
x_189 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_189, 0, x_188);
if (lean_is_scalar(x_187)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_187;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_186);
return x_190;
}
else
{
lean_object* x_191; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_167);
lean_dec(x_166);
x_191 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_173);
return x_191;
}
}
}
case 5:
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_1);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_193 = lean_ctor_get(x_1, 0);
x_194 = lean_st_ref_get(x_2, x_7);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = lean_ctor_get(x_194, 1);
x_198 = 1;
x_199 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_196, x_193, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec(x_199);
lean_ctor_set(x_1, 0, x_200);
lean_ctor_set(x_194, 0, x_1);
return x_194;
}
else
{
lean_object* x_201; 
lean_free_object(x_194);
lean_free_object(x_1);
x_201 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_197);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_194, 0);
x_203 = lean_ctor_get(x_194, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_194);
x_204 = 1;
x_205 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_202, x_193, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec(x_205);
lean_ctor_set(x_1, 0, x_206);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_1);
lean_ctor_set(x_207, 1, x_203);
return x_207;
}
else
{
lean_object* x_208; 
lean_free_object(x_1);
x_208 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_203);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_209 = lean_ctor_get(x_1, 0);
lean_inc(x_209);
lean_dec(x_1);
x_210 = lean_st_ref_get(x_2, x_7);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
x_214 = 1;
x_215 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_211, x_209, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_217, 0, x_216);
if (lean_is_scalar(x_213)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_213;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_212);
return x_218;
}
else
{
lean_object* x_219; 
lean_dec(x_213);
x_219 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_212);
return x_219;
}
}
}
default: 
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_1);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = lean_ctor_get(x_1, 0);
x_222 = lean_st_ref_get(x_2, x_7);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = 1;
x_226 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_224, x_225, x_221);
lean_ctor_set(x_1, 0, x_226);
lean_ctor_set(x_222, 0, x_1);
return x_222;
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_222, 0);
x_228 = lean_ctor_get(x_222, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_222);
x_229 = 1;
x_230 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_227, x_229, x_221);
lean_ctor_set(x_1, 0, x_230);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_1);
lean_ctor_set(x_231, 1, x_228);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_232 = lean_ctor_get(x_1, 0);
lean_inc(x_232);
lean_dec(x_1);
x_233 = lean_st_ref_get(x_2, x_7);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_236 = x_233;
} else {
 lean_dec_ref(x_233);
 x_236 = lean_box(0);
}
x_237 = 1;
x_238 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_234, x_237, x_232);
x_239 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_239, 0, x_238);
if (lean_is_scalar(x_236)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_236;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_235);
return x_240;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_normArg___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_normArg___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__2(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeCode___spec__3(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_1, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Compiler_LCNF_Internalize_internalizeLetDecl(x_16, x_2, x_3, x_4, x_5, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
case 1:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_24, x_2, x_3, x_4, x_5, x_6, x_7);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_1, 0, x_27);
lean_ctor_set(x_25, 0, x_1);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_1, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_31, x_2, x_3, x_4, x_5, x_6, x_7);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
default: 
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_39, x_2, x_3, x_4, x_5, x_6, x_7);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_ctor_set(x_1, 0, x_42);
lean_ctor_set(x_40, 0, x_1);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_1, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = l_Lean_Compiler_LCNF_Internalize_internalizeFunDecl(x_46, x_2, x_3, x_4, x_5, x_6, x_7);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_st_mk_ref(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Code_internalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Code_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_internalize_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_st_ref_get(x_2, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_15, x_9);
x_17 = lean_array_get_size(x_10);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_18, x_19, x_10, x_2, x_3, x_4, x_5, x_6, x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_11, x_2, x_3, x_4, x_5, x_6, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_1, 4, x_25);
lean_ctor_set(x_1, 3, x_21);
lean_ctor_set(x_1, 2, x_16);
lean_ctor_set(x_23, 0, x_1);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_1, 4, x_26);
lean_ctor_set(x_1, 3, x_21);
lean_ctor_set(x_1, 2, x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 2);
x_32 = lean_ctor_get(x_1, 3);
x_33 = lean_ctor_get(x_1, 4);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_36 = lean_ctor_get(x_1, 5);
lean_inc(x_36);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_37 = lean_st_ref_get(x_2, x_7);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 1;
x_41 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_38, x_40, x_31);
x_42 = lean_array_get_size(x_32);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = 0;
x_45 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Internalize_internalizeFunDecl___spec__1(x_43, x_44, x_32, x_2, x_3, x_4, x_5, x_6, x_39);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_33, x_2, x_3, x_4, x_5, x_6, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_52, 0, x_29);
lean_ctor_set(x_52, 1, x_30);
lean_ctor_set(x_52, 2, x_41);
lean_ctor_set(x_52, 3, x_46);
lean_ctor_set(x_52, 4, x_49);
lean_ctor_set(x_52, 5, x_36);
lean_ctor_set_uint8(x_52, sizeof(void*)*6, x_34);
lean_ctor_set_uint8(x_52, sizeof(void*)*6 + 1, x_35);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_internalize_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Decl_internalize_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_st_mk_ref(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_Decl_internalize_go(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_internalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_cleanup___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_cleanup___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_st_ref_take(x_5, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
x_19 = lean_unsigned_to_nat(1u);
lean_ctor_set(x_15, 1, x_19);
x_20 = lean_st_ref_set(x_5, x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(8u);
x_23 = l_Lean_mkHashMapImp___rarg(x_22);
x_24 = l_Lean_Compiler_LCNF_Decl_internalize(x_11, x_23, x_4, x_5, x_6, x_7, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_29 = lean_array_uset(x_13, x_2, x_25);
x_2 = x_28;
x_3 = x_29;
x_8 = x_26;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_st_ref_set(x_5, x_33, x_16);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(8u);
x_37 = l_Lean_mkHashMapImp___rarg(x_36);
x_38 = l_Lean_Compiler_LCNF_Decl_internalize(x_11, x_37, x_4, x_5, x_6, x_7, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
x_42 = lean_usize_add(x_2, x_41);
x_43 = lean_array_uset(x_13, x_2, x_39);
x_2 = x_42;
x_3 = x_43;
x_8 = x_40;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_cleanup___closed__1;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cleanup___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_cleanup___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_LCNF_cleanup(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_7 = lean_st_ref_take(x_3, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_cleanup___closed__3;
x_10 = lean_st_ref_set(x_3, x_9, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_get_size(x_1);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_cleanup___spec__2(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_cleanup___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_cleanup___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_cleanup___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_cleanup___spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_uniq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_take(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_10, 2);
lean_dec(x_13);
x_14 = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3;
lean_ctor_set(x_10, 2, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_cleanup___closed__1;
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 7, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Compiler_LCNF_cleanup___closed__3;
x_20 = 0;
lean_inc(x_3);
x_21 = l_Lean_Compiler_LCNF_CompilerM_run___rarg(x_18, x_19, x_20, x_2, x_3, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_3, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_25, 2);
lean_dec(x_28);
lean_ctor_set(x_25, 2, x_8);
x_29 = lean_st_ref_set(x_3, x_25, x_26);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_22);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
x_36 = lean_ctor_get(x_25, 3);
x_37 = lean_ctor_get(x_25, 4);
x_38 = lean_ctor_get(x_25, 5);
x_39 = lean_ctor_get(x_25, 6);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_40 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_8);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_38);
lean_ctor_set(x_40, 6, x_39);
x_41 = lean_st_ref_set(x_3, x_40, x_26);
lean_dec(x_3);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_21, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_st_ref_take(x_3, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_48, 2);
lean_dec(x_51);
lean_ctor_set(x_48, 2, x_8);
x_52 = lean_st_ref_set(x_3, x_48, x_49);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_45);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
x_59 = lean_ctor_get(x_48, 3);
x_60 = lean_ctor_get(x_48, 4);
x_61 = lean_ctor_get(x_48, 5);
x_62 = lean_ctor_get(x_48, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_8);
lean_ctor_set(x_63, 3, x_59);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_63, 5, x_61);
lean_ctor_set(x_63, 6, x_62);
x_64 = lean_st_ref_set(x_3, x_63, x_49);
lean_dec(x_3);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
 lean_ctor_set_tag(x_67, 1);
}
lean_ctor_set(x_67, 0, x_45);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_68 = lean_ctor_get(x_10, 0);
x_69 = lean_ctor_get(x_10, 1);
x_70 = lean_ctor_get(x_10, 3);
x_71 = lean_ctor_get(x_10, 4);
x_72 = lean_ctor_get(x_10, 5);
x_73 = lean_ctor_get(x_10, 6);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_10);
x_74 = l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3;
x_75 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_69);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_75, 3, x_70);
lean_ctor_set(x_75, 4, x_71);
lean_ctor_set(x_75, 5, x_72);
lean_ctor_set(x_75, 6, x_73);
x_76 = lean_st_ref_set(x_3, x_75, x_11);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Compiler_LCNF_cleanup___closed__1;
x_79 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_internalize___boxed), 7, 2);
lean_closure_set(x_79, 0, x_1);
lean_closure_set(x_79, 1, x_78);
x_80 = l_Lean_Compiler_LCNF_cleanup___closed__3;
x_81 = 0;
lean_inc(x_3);
x_82 = l_Lean_Compiler_LCNF_CompilerM_run___rarg(x_79, x_80, x_81, x_2, x_3, x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_take(x_3, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 5);
lean_inc(x_92);
x_93 = lean_ctor_get(x_86, 6);
lean_inc(x_93);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 lean_ctor_release(x_86, 6);
 x_94 = x_86;
} else {
 lean_dec_ref(x_86);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 7, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_89);
lean_ctor_set(x_95, 2, x_8);
lean_ctor_set(x_95, 3, x_90);
lean_ctor_set(x_95, 4, x_91);
lean_ctor_set(x_95, 5, x_92);
lean_ctor_set(x_95, 6, x_93);
x_96 = lean_st_ref_set(x_3, x_95, x_87);
lean_dec(x_3);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_83);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_100 = lean_ctor_get(x_82, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_82, 1);
lean_inc(x_101);
lean_dec(x_82);
x_102 = lean_st_ref_take(x_3, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 5);
lean_inc(x_109);
x_110 = lean_ctor_get(x_103, 6);
lean_inc(x_110);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 lean_ctor_release(x_103, 6);
 x_111 = x_103;
} else {
 lean_dec_ref(x_103);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 7, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set(x_112, 1, x_106);
lean_ctor_set(x_112, 2, x_8);
lean_ctor_set(x_112, 3, x_107);
lean_ctor_set(x_112, 4, x_108);
lean_ctor_set(x_112, 5, x_109);
lean_ctor_set(x_112, 6, x_110);
x_113 = lean_st_ref_set(x_3, x_112, x_104);
lean_dec(x_3);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
 lean_ctor_set_tag(x_116, 1);
}
lean_ctor_set(x_116, 0, x_100);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue___closed__1);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstInternalizeMTrue);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1 = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM___closed__1);
l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM = _init_l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM();
lean_mark_persistent(l_Lean_Compiler_LCNF_Internalize_instMonadFVarSubstStateInternalizeM);
l_Lean_Compiler_LCNF_cleanup___closed__1 = _init_l_Lean_Compiler_LCNF_cleanup___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_cleanup___closed__1);
l_Lean_Compiler_LCNF_cleanup___closed__2 = _init_l_Lean_Compiler_LCNF_cleanup___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_cleanup___closed__2);
l_Lean_Compiler_LCNF_cleanup___closed__3 = _init_l_Lean_Compiler_LCNF_cleanup___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_cleanup___closed__3);
l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1 = _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__1);
l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2 = _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__2);
l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3 = _init_l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_normalizeFVarIds___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
