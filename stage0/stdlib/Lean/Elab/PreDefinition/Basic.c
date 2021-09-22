// Lean compiler output
// Module: Lean.Elab.PreDefinition.Basic
// Imports: Init Lean.Util.SCC Lean.Meta.AbstractNestedProofs Lean.Elab.Term Lean.Elab.DefView Lean.Elab.PreDefinition.MkInhabitant
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___boxed__const__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_addAndCompileUnsafe___spec__1(uint8_t, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls___boxed__const__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
static uint64_t l_Lean_Elab_instInhabitedPreDefinition___closed__3;
uint32_t l_UInt32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedPreDefinition;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__4(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_addAndCompileUnsafe___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 0;
x_5 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
static uint64_t _init_l_Lean_Elab_instInhabitedPreDefinition___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__4() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_instInhabitedPreDefinition___closed__3;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lean_Elab_instInhabitedPreDefinition___closed__2;
x_5 = lean_box(0);
x_6 = l_Lean_Elab_instInhabitedPreDefinition___closed__4;
x_7 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_6);
lean_ctor_set(x_7, 5, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedPreDefinition___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 < x_1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = x_3;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = x_14;
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get(x_17, 5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_Meta_instantiateMVars(x_23, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Meta_instantiateMVars(x_24, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set(x_17, 5, x_29);
lean_ctor_set(x_17, 4, x_26);
x_31 = 1;
x_32 = x_2 + x_31;
x_33 = x_17;
x_34 = lean_array_uset(x_16, x_2, x_33);
x_2 = x_32;
x_3 = x_34;
x_10 = x_30;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_26);
lean_free_object(x_17);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_17);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get_uint8(x_17, sizeof(void*)*6);
x_46 = lean_ctor_get(x_17, 1);
x_47 = lean_ctor_get(x_17, 2);
x_48 = lean_ctor_get(x_17, 3);
x_49 = lean_ctor_get(x_17, 4);
x_50 = lean_ctor_get(x_17, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_44);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l_Lean_Meta_instantiateMVars(x_49, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_54 = l_Lean_Meta_instantiateMVars(x_50, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_47);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set(x_57, 4, x_52);
lean_ctor_set(x_57, 5, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*6, x_45);
x_58 = 1;
x_59 = x_2 + x_58;
x_60 = x_57;
x_61 = lean_array_uset(x_16, x_2, x_60);
x_2 = x_59;
x_3 = x_61;
x_10 = x_56;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_52);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_51, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_69 = x_51;
} else {
 lean_dec_ref(x_51);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_instantiateMVarsAtPreDecls___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = x_1;
x_12 = lean_box_usize(x_10);
x_13 = l_Lean_Elab_instantiateMVarsAtPreDecls___boxed__const__1;
x_14 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed), 10, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_11);
x_15 = x_14;
x_16 = lean_apply_7(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 < x_1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = x_15;
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_18, 4);
x_21 = lean_ctor_get(x_18, 5);
x_22 = l_Lean_Elab_Term_levelMVarToParam_x27(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_levelMVarToParam_x27(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_18, 5, x_26);
lean_ctor_set(x_18, 4, x_23);
x_28 = 1;
x_29 = x_2 + x_28;
x_30 = x_18;
x_31 = lean_array_uset(x_17, x_2, x_30);
x_2 = x_29;
x_3 = x_31;
x_11 = x_27;
goto _start;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get_uint8(x_18, sizeof(void*)*6);
x_35 = lean_ctor_get(x_18, 1);
x_36 = lean_ctor_get(x_18, 2);
x_37 = lean_ctor_get(x_18, 3);
x_38 = lean_ctor_get(x_18, 4);
x_39 = lean_ctor_get(x_18, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_dec(x_18);
x_40 = l_Lean_Elab_Term_levelMVarToParam_x27(x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Term_levelMVarToParam_x27(x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*6, x_34);
x_47 = 1;
x_48 = x_2 + x_47;
x_49 = x_46;
x_50 = lean_array_uset(x_17, x_2, x_49);
x_2 = x_48;
x_3 = x_50;
x_11 = x_45;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = x_1;
x_13 = lean_box_usize(x_11);
x_14 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___boxed__const__1;
x_15 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1___boxed), 11, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_12);
x_16 = x_15;
x_17 = lean_apply_8(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___spec__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_13);
x_15 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
x_16 = l_Lean_CollectLevelParams_main(x_15, x_4);
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_CollectLevelParams_main(x_17, x_16);
x_19 = 1;
x_20 = x_3 + x_19;
x_3 = x_20;
x_4 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1;
x_2 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2;
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(x_1, x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__2(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_8);
lean_dec(x_6);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__2(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_8);
lean_dec(x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
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
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_215; lean_object* x_216; size_t x_217; uint8_t x_218; 
x_6 = lean_ptr_addr(x_4);
x_7 = x_3 == 0 ? x_6 : x_6 % x_3;
x_215 = lean_ctor_get(x_5, 0);
lean_inc(x_215);
x_216 = lean_array_uget(x_215, x_7);
lean_dec(x_215);
x_217 = lean_ptr_addr(x_216);
lean_dec(x_216);
x_218 = x_217 == x_6;
if (x_218 == 0)
{
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_4, 0);
lean_inc(x_219);
x_220 = lean_array_get_size(x_1);
x_221 = lean_unsigned_to_nat(0u);
x_222 = lean_nat_dec_lt(x_221, x_220);
if (x_222 == 0)
{
lean_object* x_223; 
lean_dec(x_220);
lean_dec(x_219);
x_223 = lean_box(0);
x_8 = x_223;
goto block_214;
}
else
{
uint8_t x_224; 
x_224 = lean_nat_dec_le(x_220, x_220);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_220);
lean_dec(x_219);
x_225 = lean_box(0);
x_8 = x_225;
goto block_214;
}
else
{
size_t x_226; size_t x_227; uint8_t x_228; 
x_226 = 0;
x_227 = lean_usize_of_nat(x_220);
lean_dec(x_220);
x_228 = l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(x_219, x_1, x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_219);
x_229 = lean_box(0);
x_8 = x_229;
goto block_214;
}
else
{
lean_object* x_230; uint8_t x_231; 
x_230 = l_Lean_mkConst(x_219, x_2);
x_231 = !lean_is_exclusive(x_5);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_5, 0);
x_233 = lean_ctor_get(x_5, 1);
x_234 = lean_array_uset(x_232, x_7, x_4);
lean_inc(x_230);
x_235 = lean_array_uset(x_233, x_7, x_230);
lean_ctor_set(x_5, 1, x_235);
lean_ctor_set(x_5, 0, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_230);
lean_ctor_set(x_236, 1, x_5);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_237 = lean_ctor_get(x_5, 0);
x_238 = lean_ctor_get(x_5, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_5);
x_239 = lean_array_uset(x_237, x_7, x_4);
lean_inc(x_230);
x_240 = lean_array_uset(x_238, x_7, x_230);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_230);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
}
else
{
lean_object* x_243; 
x_243 = lean_box(0);
x_8 = x_243;
goto block_214;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_4);
lean_dec(x_2);
x_244 = lean_ctor_get(x_5, 1);
lean_inc(x_244);
x_245 = lean_array_uget(x_244, x_7);
lean_dec(x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_5);
return x_246;
}
block_214:
{
lean_dec(x_8);
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_9);
lean_inc(x_2);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_9, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_10, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set_uint64(x_19, sizeof(void*)*2, x_11);
x_20 = lean_expr_update_app(x_19, x_13, x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_array_uset(x_22, x_7, x_4);
lean_inc(x_20);
x_25 = lean_array_uset(x_23, x_7, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_24);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_array_uset(x_26, x_7, x_4);
lean_inc(x_20);
x_29 = lean_array_uset(x_27, x_7, x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set_uint64(x_33, sizeof(void*)*2, x_11);
x_34 = lean_expr_update_app(x_33, x_13, x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_37 = x_32;
} else {
 lean_dec_ref(x_32);
 x_37 = lean_box(0);
}
x_38 = lean_array_uset(x_35, x_7, x_4);
lean_inc(x_34);
x_39 = lean_array_uset(x_36, x_7, x_34);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_43);
lean_inc(x_2);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_43, x_5);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_44);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_44, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_53 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set_uint64(x_53, sizeof(void*)*3, x_45);
x_54 = (uint8_t)((x_45 << 24) >> 61);
x_55 = lean_expr_update_lambda(x_53, x_54, x_47, x_51);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
x_59 = lean_array_uset(x_57, x_7, x_4);
lean_inc(x_55);
x_60 = lean_array_uset(x_58, x_7, x_55);
lean_ctor_set(x_52, 1, x_60);
lean_ctor_set(x_52, 0, x_59);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_array_uset(x_61, x_7, x_4);
lean_inc(x_55);
x_64 = lean_array_uset(x_62, x_7, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_49, 1, x_65);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_68 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_43);
lean_ctor_set(x_68, 2, x_44);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_45);
x_69 = (uint8_t)((x_45 << 24) >> 61);
x_70 = lean_expr_update_lambda(x_68, x_69, x_47, x_66);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
x_74 = lean_array_uset(x_71, x_7, x_4);
lean_inc(x_70);
x_75 = lean_array_uset(x_72, x_7, x_70);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
case 7:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_79);
lean_inc(x_2);
x_82 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_79, x_5);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_80);
x_85 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_79);
lean_ctor_set(x_89, 2, x_80);
lean_ctor_set_uint64(x_89, sizeof(void*)*3, x_81);
x_90 = (uint8_t)((x_81 << 24) >> 61);
x_91 = lean_expr_update_forall(x_89, x_90, x_83, x_87);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
x_95 = lean_array_uset(x_93, x_7, x_4);
lean_inc(x_91);
x_96 = lean_array_uset(x_94, x_7, x_91);
lean_ctor_set(x_88, 1, x_96);
lean_ctor_set(x_88, 0, x_95);
lean_ctor_set(x_85, 0, x_91);
return x_85;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_array_uset(x_97, x_7, x_4);
lean_inc(x_91);
x_100 = lean_array_uset(x_98, x_7, x_91);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_85, 1, x_101);
lean_ctor_set(x_85, 0, x_91);
return x_85;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_102 = lean_ctor_get(x_85, 0);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_85);
x_104 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_104, 0, x_78);
lean_ctor_set(x_104, 1, x_79);
lean_ctor_set(x_104, 2, x_80);
lean_ctor_set_uint64(x_104, sizeof(void*)*3, x_81);
x_105 = (uint8_t)((x_81 << 24) >> 61);
x_106 = lean_expr_update_forall(x_104, x_105, x_83, x_102);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = lean_array_uset(x_107, x_7, x_4);
lean_inc(x_106);
x_111 = lean_array_uset(x_108, x_7, x_106);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
case 8:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint64_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_114 = lean_ctor_get(x_4, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_4, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_4, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_4, 3);
lean_inc(x_117);
x_118 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
lean_inc(x_115);
lean_inc(x_2);
x_119 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_115, x_5);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_116);
lean_inc(x_2);
x_122 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_116, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_117);
x_125 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_117, x_124);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
x_129 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_129, 0, x_114);
lean_ctor_set(x_129, 1, x_115);
lean_ctor_set(x_129, 2, x_116);
lean_ctor_set(x_129, 3, x_117);
lean_ctor_set_uint64(x_129, sizeof(void*)*4, x_118);
x_130 = lean_expr_update_let(x_129, x_120, x_123, x_127);
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
x_134 = lean_array_uset(x_132, x_7, x_4);
lean_inc(x_130);
x_135 = lean_array_uset(x_133, x_7, x_130);
lean_ctor_set(x_128, 1, x_135);
lean_ctor_set(x_128, 0, x_134);
lean_ctor_set(x_125, 0, x_130);
return x_125;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_128, 0);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_128);
x_138 = lean_array_uset(x_136, x_7, x_4);
lean_inc(x_130);
x_139 = lean_array_uset(x_137, x_7, x_130);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_125, 1, x_140);
lean_ctor_set(x_125, 0, x_130);
return x_125;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_125, 0);
x_142 = lean_ctor_get(x_125, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_125);
x_143 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_143, 0, x_114);
lean_ctor_set(x_143, 1, x_115);
lean_ctor_set(x_143, 2, x_116);
lean_ctor_set(x_143, 3, x_117);
lean_ctor_set_uint64(x_143, sizeof(void*)*4, x_118);
x_144 = lean_expr_update_let(x_143, x_120, x_123, x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_array_uset(x_145, x_7, x_4);
lean_inc(x_144);
x_149 = lean_array_uset(x_146, x_7, x_144);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
case 10:
{
lean_object* x_152; lean_object* x_153; uint64_t x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_4, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_4, 1);
lean_inc(x_153);
x_154 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_153);
x_155 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_153, x_5);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_159, 0, x_152);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set_uint64(x_159, sizeof(void*)*2, x_154);
x_160 = lean_expr_update_mdata(x_159, x_157);
x_161 = !lean_is_exclusive(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_158, 0);
x_163 = lean_ctor_get(x_158, 1);
x_164 = lean_array_uset(x_162, x_7, x_4);
lean_inc(x_160);
x_165 = lean_array_uset(x_163, x_7, x_160);
lean_ctor_set(x_158, 1, x_165);
lean_ctor_set(x_158, 0, x_164);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_array_uset(x_166, x_7, x_4);
lean_inc(x_160);
x_169 = lean_array_uset(x_167, x_7, x_160);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_155, 1, x_170);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_171 = lean_ctor_get(x_155, 0);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_155);
x_173 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_173, 0, x_152);
lean_ctor_set(x_173, 1, x_153);
lean_ctor_set_uint64(x_173, sizeof(void*)*2, x_154);
x_174 = lean_expr_update_mdata(x_173, x_171);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
 x_177 = lean_box(0);
}
x_178 = lean_array_uset(x_175, x_7, x_4);
lean_inc(x_174);
x_179 = lean_array_uset(x_176, x_7, x_174);
if (lean_is_scalar(x_177)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_177;
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
case 11:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint64_t x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_4, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_4, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_4, 2);
lean_inc(x_184);
x_185 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_184);
x_186 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_184, x_5);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = lean_ctor_get(x_186, 1);
x_190 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_183);
lean_ctor_set(x_190, 2, x_184);
lean_ctor_set_uint64(x_190, sizeof(void*)*3, x_185);
x_191 = lean_expr_update_proj(x_190, x_188);
x_192 = !lean_is_exclusive(x_189);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_189, 0);
x_194 = lean_ctor_get(x_189, 1);
x_195 = lean_array_uset(x_193, x_7, x_4);
lean_inc(x_191);
x_196 = lean_array_uset(x_194, x_7, x_191);
lean_ctor_set(x_189, 1, x_196);
lean_ctor_set(x_189, 0, x_195);
lean_ctor_set(x_186, 0, x_191);
return x_186;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_189, 0);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_189);
x_199 = lean_array_uset(x_197, x_7, x_4);
lean_inc(x_191);
x_200 = lean_array_uset(x_198, x_7, x_191);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_186, 1, x_201);
lean_ctor_set(x_186, 0, x_191);
return x_186;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_202 = lean_ctor_get(x_186, 0);
x_203 = lean_ctor_get(x_186, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_186);
x_204 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_204, 0, x_182);
lean_ctor_set(x_204, 1, x_183);
lean_ctor_set(x_204, 2, x_184);
lean_ctor_set_uint64(x_204, sizeof(void*)*3, x_185);
x_205 = lean_expr_update_proj(x_204, x_202);
x_206 = lean_ctor_get(x_203, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_208 = x_203;
} else {
 lean_dec_ref(x_203);
 x_208 = lean_box(0);
}
x_209 = lean_array_uset(x_206, x_7, x_4);
lean_inc(x_205);
x_210 = lean_array_uset(x_207, x_7, x_205);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
default: 
{
lean_object* x_213; 
lean_dec(x_2);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_4);
lean_ctor_set(x_213, 1, x_5);
return x_213;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_215; lean_object* x_216; size_t x_217; uint8_t x_218; 
x_6 = lean_ptr_addr(x_4);
x_7 = x_3 == 0 ? x_6 : x_6 % x_3;
x_215 = lean_ctor_get(x_5, 0);
lean_inc(x_215);
x_216 = lean_array_uget(x_215, x_7);
lean_dec(x_215);
x_217 = lean_ptr_addr(x_216);
lean_dec(x_216);
x_218 = x_217 == x_6;
if (x_218 == 0)
{
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_4, 0);
lean_inc(x_219);
x_220 = lean_array_get_size(x_1);
x_221 = lean_unsigned_to_nat(0u);
x_222 = lean_nat_dec_lt(x_221, x_220);
if (x_222 == 0)
{
lean_object* x_223; 
lean_dec(x_220);
lean_dec(x_219);
x_223 = lean_box(0);
x_8 = x_223;
goto block_214;
}
else
{
uint8_t x_224; 
x_224 = lean_nat_dec_le(x_220, x_220);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_220);
lean_dec(x_219);
x_225 = lean_box(0);
x_8 = x_225;
goto block_214;
}
else
{
size_t x_226; size_t x_227; uint8_t x_228; 
x_226 = 0;
x_227 = lean_usize_of_nat(x_220);
lean_dec(x_220);
x_228 = l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(x_219, x_1, x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_219);
x_229 = lean_box(0);
x_8 = x_229;
goto block_214;
}
else
{
lean_object* x_230; uint8_t x_231; 
x_230 = l_Lean_mkConst(x_219, x_2);
x_231 = !lean_is_exclusive(x_5);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_5, 0);
x_233 = lean_ctor_get(x_5, 1);
x_234 = lean_array_uset(x_232, x_7, x_4);
lean_inc(x_230);
x_235 = lean_array_uset(x_233, x_7, x_230);
lean_ctor_set(x_5, 1, x_235);
lean_ctor_set(x_5, 0, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_230);
lean_ctor_set(x_236, 1, x_5);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_237 = lean_ctor_get(x_5, 0);
x_238 = lean_ctor_get(x_5, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_5);
x_239 = lean_array_uset(x_237, x_7, x_4);
lean_inc(x_230);
x_240 = lean_array_uset(x_238, x_7, x_230);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_230);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
}
else
{
lean_object* x_243; 
x_243 = lean_box(0);
x_8 = x_243;
goto block_214;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_4);
lean_dec(x_2);
x_244 = lean_ctor_get(x_5, 1);
lean_inc(x_244);
x_245 = lean_array_uget(x_244, x_7);
lean_dec(x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_5);
return x_246;
}
block_214:
{
lean_dec(x_8);
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_9);
lean_inc(x_2);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_9, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_10, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set_uint64(x_19, sizeof(void*)*2, x_11);
x_20 = lean_expr_update_app(x_19, x_13, x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_array_uset(x_22, x_7, x_4);
lean_inc(x_20);
x_25 = lean_array_uset(x_23, x_7, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_24);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_array_uset(x_26, x_7, x_4);
lean_inc(x_20);
x_29 = lean_array_uset(x_27, x_7, x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set_uint64(x_33, sizeof(void*)*2, x_11);
x_34 = lean_expr_update_app(x_33, x_13, x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_37 = x_32;
} else {
 lean_dec_ref(x_32);
 x_37 = lean_box(0);
}
x_38 = lean_array_uset(x_35, x_7, x_4);
lean_inc(x_34);
x_39 = lean_array_uset(x_36, x_7, x_34);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_43);
lean_inc(x_2);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_43, x_5);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_44);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_44, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_53 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set_uint64(x_53, sizeof(void*)*3, x_45);
x_54 = (uint8_t)((x_45 << 24) >> 61);
x_55 = lean_expr_update_lambda(x_53, x_54, x_47, x_51);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
x_59 = lean_array_uset(x_57, x_7, x_4);
lean_inc(x_55);
x_60 = lean_array_uset(x_58, x_7, x_55);
lean_ctor_set(x_52, 1, x_60);
lean_ctor_set(x_52, 0, x_59);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_array_uset(x_61, x_7, x_4);
lean_inc(x_55);
x_64 = lean_array_uset(x_62, x_7, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_49, 1, x_65);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_68 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_43);
lean_ctor_set(x_68, 2, x_44);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_45);
x_69 = (uint8_t)((x_45 << 24) >> 61);
x_70 = lean_expr_update_lambda(x_68, x_69, x_47, x_66);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
x_74 = lean_array_uset(x_71, x_7, x_4);
lean_inc(x_70);
x_75 = lean_array_uset(x_72, x_7, x_70);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
case 7:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_79);
lean_inc(x_2);
x_82 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_79, x_5);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_80);
x_85 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_79);
lean_ctor_set(x_89, 2, x_80);
lean_ctor_set_uint64(x_89, sizeof(void*)*3, x_81);
x_90 = (uint8_t)((x_81 << 24) >> 61);
x_91 = lean_expr_update_forall(x_89, x_90, x_83, x_87);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
x_95 = lean_array_uset(x_93, x_7, x_4);
lean_inc(x_91);
x_96 = lean_array_uset(x_94, x_7, x_91);
lean_ctor_set(x_88, 1, x_96);
lean_ctor_set(x_88, 0, x_95);
lean_ctor_set(x_85, 0, x_91);
return x_85;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_array_uset(x_97, x_7, x_4);
lean_inc(x_91);
x_100 = lean_array_uset(x_98, x_7, x_91);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_85, 1, x_101);
lean_ctor_set(x_85, 0, x_91);
return x_85;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_102 = lean_ctor_get(x_85, 0);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_85);
x_104 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_104, 0, x_78);
lean_ctor_set(x_104, 1, x_79);
lean_ctor_set(x_104, 2, x_80);
lean_ctor_set_uint64(x_104, sizeof(void*)*3, x_81);
x_105 = (uint8_t)((x_81 << 24) >> 61);
x_106 = lean_expr_update_forall(x_104, x_105, x_83, x_102);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = lean_array_uset(x_107, x_7, x_4);
lean_inc(x_106);
x_111 = lean_array_uset(x_108, x_7, x_106);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
case 8:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint64_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_114 = lean_ctor_get(x_4, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_4, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_4, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_4, 3);
lean_inc(x_117);
x_118 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
lean_inc(x_115);
lean_inc(x_2);
x_119 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_115, x_5);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_116);
lean_inc(x_2);
x_122 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_116, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_117);
x_125 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_117, x_124);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
x_129 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_129, 0, x_114);
lean_ctor_set(x_129, 1, x_115);
lean_ctor_set(x_129, 2, x_116);
lean_ctor_set(x_129, 3, x_117);
lean_ctor_set_uint64(x_129, sizeof(void*)*4, x_118);
x_130 = lean_expr_update_let(x_129, x_120, x_123, x_127);
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
x_134 = lean_array_uset(x_132, x_7, x_4);
lean_inc(x_130);
x_135 = lean_array_uset(x_133, x_7, x_130);
lean_ctor_set(x_128, 1, x_135);
lean_ctor_set(x_128, 0, x_134);
lean_ctor_set(x_125, 0, x_130);
return x_125;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_128, 0);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_128);
x_138 = lean_array_uset(x_136, x_7, x_4);
lean_inc(x_130);
x_139 = lean_array_uset(x_137, x_7, x_130);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_125, 1, x_140);
lean_ctor_set(x_125, 0, x_130);
return x_125;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_125, 0);
x_142 = lean_ctor_get(x_125, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_125);
x_143 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_143, 0, x_114);
lean_ctor_set(x_143, 1, x_115);
lean_ctor_set(x_143, 2, x_116);
lean_ctor_set(x_143, 3, x_117);
lean_ctor_set_uint64(x_143, sizeof(void*)*4, x_118);
x_144 = lean_expr_update_let(x_143, x_120, x_123, x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_array_uset(x_145, x_7, x_4);
lean_inc(x_144);
x_149 = lean_array_uset(x_146, x_7, x_144);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
case 10:
{
lean_object* x_152; lean_object* x_153; uint64_t x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_4, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_4, 1);
lean_inc(x_153);
x_154 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_153);
x_155 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_153, x_5);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_159, 0, x_152);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set_uint64(x_159, sizeof(void*)*2, x_154);
x_160 = lean_expr_update_mdata(x_159, x_157);
x_161 = !lean_is_exclusive(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_158, 0);
x_163 = lean_ctor_get(x_158, 1);
x_164 = lean_array_uset(x_162, x_7, x_4);
lean_inc(x_160);
x_165 = lean_array_uset(x_163, x_7, x_160);
lean_ctor_set(x_158, 1, x_165);
lean_ctor_set(x_158, 0, x_164);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_array_uset(x_166, x_7, x_4);
lean_inc(x_160);
x_169 = lean_array_uset(x_167, x_7, x_160);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_155, 1, x_170);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_171 = lean_ctor_get(x_155, 0);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_155);
x_173 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_173, 0, x_152);
lean_ctor_set(x_173, 1, x_153);
lean_ctor_set_uint64(x_173, sizeof(void*)*2, x_154);
x_174 = lean_expr_update_mdata(x_173, x_171);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
 x_177 = lean_box(0);
}
x_178 = lean_array_uset(x_175, x_7, x_4);
lean_inc(x_174);
x_179 = lean_array_uset(x_176, x_7, x_174);
if (lean_is_scalar(x_177)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_177;
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
case 11:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint64_t x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_4, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_4, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_4, 2);
lean_inc(x_184);
x_185 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_184);
x_186 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_184, x_5);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = lean_ctor_get(x_186, 1);
x_190 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_183);
lean_ctor_set(x_190, 2, x_184);
lean_ctor_set_uint64(x_190, sizeof(void*)*3, x_185);
x_191 = lean_expr_update_proj(x_190, x_188);
x_192 = !lean_is_exclusive(x_189);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_189, 0);
x_194 = lean_ctor_get(x_189, 1);
x_195 = lean_array_uset(x_193, x_7, x_4);
lean_inc(x_191);
x_196 = lean_array_uset(x_194, x_7, x_191);
lean_ctor_set(x_189, 1, x_196);
lean_ctor_set(x_189, 0, x_195);
lean_ctor_set(x_186, 0, x_191);
return x_186;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_189, 0);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_189);
x_199 = lean_array_uset(x_197, x_7, x_4);
lean_inc(x_191);
x_200 = lean_array_uset(x_198, x_7, x_191);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_186, 1, x_201);
lean_ctor_set(x_186, 0, x_191);
return x_186;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_202 = lean_ctor_get(x_186, 0);
x_203 = lean_ctor_get(x_186, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_186);
x_204 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_204, 0, x_182);
lean_ctor_set(x_204, 1, x_183);
lean_ctor_set(x_204, 2, x_184);
lean_ctor_set_uint64(x_204, sizeof(void*)*3, x_185);
x_205 = lean_expr_update_proj(x_204, x_202);
x_206 = lean_ctor_get(x_203, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_208 = x_203;
} else {
 lean_dec_ref(x_203);
 x_208 = lean_box(0);
}
x_209 = lean_array_uset(x_206, x_7, x_4);
lean_inc(x_205);
x_210 = lean_array_uset(x_207, x_7, x_205);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
default: 
{
lean_object* x_213; 
lean_dec(x_2);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_4);
lean_ctor_set(x_213, 1, x_5);
return x_213;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = x_6;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_uget(x_6, x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_6, x_5, x_10);
x_12 = x_9;
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = lean_ctor_get(x_12, 5);
x_16 = lean_ctor_get(x_12, 1);
lean_dec(x_16);
x_17 = 8192;
x_18 = l_Lean_Expr_ReplaceImpl_initCache;
lean_inc(x_3);
x_19 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_3, x_17, x_14, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_3);
x_21 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_3, x_17, x_15, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_2);
lean_ctor_set(x_12, 5, x_22);
lean_ctor_set(x_12, 4, x_20);
lean_ctor_set(x_12, 1, x_2);
x_23 = 1;
x_24 = x_5 + x_23;
x_25 = x_12;
x_26 = lean_array_uset(x_11, x_5, x_25);
x_5 = x_24;
x_6 = x_26;
goto _start;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get_uint8(x_12, sizeof(void*)*6);
x_30 = lean_ctor_get(x_12, 2);
x_31 = lean_ctor_get(x_12, 3);
x_32 = lean_ctor_get(x_12, 4);
x_33 = lean_ctor_get(x_12, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_dec(x_12);
x_34 = 8192;
x_35 = l_Lean_Expr_ReplaceImpl_initCache;
lean_inc(x_3);
x_36 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_3, x_34, x_32, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_3);
x_38 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_3, x_34, x_33, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
lean_inc(x_2);
x_40 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_2);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_29);
x_41 = 1;
x_42 = x_5 + x_41;
x_43 = x_40;
x_44 = lean_array_uset(x_11, x_5, x_43);
x_5 = x_42;
x_6 = x_44;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_14);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_1);
x_19 = x_1;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_13, x_15, x_17, x_18, x_19);
lean_dec(x_1);
x_21 = x_20;
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_box(0);
lean_inc(x_22);
x_25 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_22, x_24);
x_26 = lean_array_get_size(x_1);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
lean_inc(x_1);
x_29 = x_1;
x_30 = l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_22, x_25, x_27, x_28, x_29);
lean_dec(x_1);
x_31 = x_30;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_fixLevelParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_4 < x_3;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_19 = l_Lean_Elab_Term_applyAttributesAt(x_16, x_18, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = x_4 + x_21;
x_23 = lean_box(0);
x_4 = x_22;
x_5 = x_23;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_box(0);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(x_2, x_1, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(x_13, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_applyAttributesOf(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_abstractNestedProofs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
x_14 = l_Lean_Elab_DefKind_isTheorem(x_8);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Elab_DefKind_isExample(x_8);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
lean_inc(x_11);
x_23 = l_Lean_Meta_abstractNestedProofs(x_11, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_1, 5, x_25);
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
lean_ctor_set(x_1, 5, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_1);
lean_inc(x_11);
x_33 = l_Lean_Meta_abstractNestedProofs(x_11, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_9);
lean_ctor_set(x_37, 2, x_10);
lean_ctor_set(x_37, 3, x_11);
lean_ctor_set(x_37, 4, x_12);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_8);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_6);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 3);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 3);
x_18 = l_Lean_replaceRef(x_7, x_17);
lean_dec(x_17);
lean_ctor_set(x_4, 3, x_18);
x_19 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_15, x_2, x_3, x_4, x_5, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_ctor_get(x_4, 4);
x_25 = lean_ctor_get(x_4, 5);
x_26 = lean_ctor_get(x_4, 6);
x_27 = lean_ctor_get(x_4, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_28 = l_Lean_replaceRef(x_7, x_23);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_27);
x_30 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_15, x_2, x_3, x_29, x_5, x_6);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addAsAxiom(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_3 = l_Lean_Elab_DefKind_isTheorem(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l_Lean_Elab_applyAttributesOf(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lean_replaceRef(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_ctor_set(x_7, 3, x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_abstractNestedProofs(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_53; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get_uint8(x_15, sizeof(void*)*6);
x_53 = lean_box(x_21);
switch (lean_obj_tag(x_53)) {
case 1:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_20);
x_54 = lean_ctor_get(x_15, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_15, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_15, 4);
lean_inc(x_56);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_ctor_get(x_15, 5);
lean_inc(x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_22 = x_60;
goto block_52;
}
case 3:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_20);
x_61 = lean_ctor_get(x_15, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_15, 4);
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_ctor_get(x_15, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_15, 2);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*2 + 3);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*2, x_67);
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_22 = x_69;
goto block_52;
}
case 4:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_20);
x_70 = lean_ctor_get(x_15, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_15, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_15, 4);
lean_inc(x_72);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_ctor_get(x_15, 2);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_74, sizeof(void*)*2 + 3);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_15, 5);
lean_inc(x_76);
x_77 = lean_box(1);
x_78 = 1;
x_79 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*3, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_22 = x_80;
goto block_52;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_15, 5);
lean_inc(x_81);
x_82 = lean_box(1);
x_83 = 0;
x_84 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_84, 0, x_73);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_22 = x_85;
goto block_52;
}
}
default: 
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint32_t x_92; uint32_t x_93; uint32_t x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_53);
x_86 = lean_ctor_get(x_15, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_15, 4);
lean_inc(x_88);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set(x_89, 2, x_88);
x_90 = lean_ctor_get(x_15, 5);
lean_inc(x_90);
lean_inc(x_90);
x_91 = l_Lean_getMaxHeight(x_20, x_90);
x_92 = lean_unbox_uint32(x_91);
lean_dec(x_91);
x_93 = 1;
x_94 = x_92 + x_93;
x_95 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_95, 0, x_94);
x_96 = lean_ctor_get(x_15, 2);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_96, sizeof(void*)*2 + 3);
lean_dec(x_96);
if (x_97 == 0)
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_98 = 1;
x_99 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_90);
lean_ctor_set(x_99, 2, x_95);
lean_ctor_set_uint8(x_99, sizeof(void*)*3, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_22 = x_100;
goto block_52;
}
else
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_101 = 0;
x_102 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_90);
lean_ctor_set(x_102, 2, x_95);
lean_ctor_set_uint8(x_102, sizeof(void*)*3, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_22 = x_103;
goto block_52;
}
}
}
block_52:
{
lean_object* x_23; 
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_22);
x_23 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
lean_inc(x_15);
x_26 = lean_array_push(x_25, x_15);
x_27 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_28 = l_Lean_Elab_applyAttributesOf(x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_28) == 0)
{
if (x_2 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = 1;
x_31 = l_Lean_Elab_applyAttributesOf(x_26, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_26);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_15);
lean_dec(x_15);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; 
lean_dec(x_22);
x_34 = 1;
x_35 = l_Lean_Elab_applyAttributesOf(x_26, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_26);
return x_35;
}
else
{
lean_object* x_36; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_36 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = l_Lean_Elab_applyAttributesOf(x_26, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_26);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
return x_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_28, 0);
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_28);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
return x_23;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_23, 0);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_23);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_14);
if (x_104 == 0)
{
return x_14;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_14, 0);
x_106 = lean_ctor_get(x_14, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_14);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_108 = lean_ctor_get(x_7, 0);
x_109 = lean_ctor_get(x_7, 1);
x_110 = lean_ctor_get(x_7, 2);
x_111 = lean_ctor_get(x_7, 3);
x_112 = lean_ctor_get(x_7, 4);
x_113 = lean_ctor_get(x_7, 5);
x_114 = lean_ctor_get(x_7, 6);
x_115 = lean_ctor_get(x_7, 7);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_7);
x_116 = l_Lean_replaceRef(x_10, x_111);
lean_dec(x_111);
lean_dec(x_10);
x_117 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_117, 0, x_108);
lean_ctor_set(x_117, 1, x_109);
lean_ctor_set(x_117, 2, x_110);
lean_ctor_set(x_117, 3, x_116);
lean_ctor_set(x_117, 4, x_112);
lean_ctor_set(x_117, 5, x_113);
lean_ctor_set(x_117, 6, x_114);
lean_ctor_set(x_117, 7, x_115);
lean_inc(x_8);
lean_inc(x_117);
lean_inc(x_6);
lean_inc(x_5);
x_118 = l_Lean_Elab_abstractNestedProofs(x_1, x_5, x_6, x_117, x_8, x_9);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_157; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_st_ref_get(x_8, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get_uint8(x_119, sizeof(void*)*6);
x_157 = lean_box(x_125);
switch (lean_obj_tag(x_157)) {
case 1:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_124);
x_158 = lean_ctor_get(x_119, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_119, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_119, 4);
lean_inc(x_160);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_ctor_get(x_119, 5);
lean_inc(x_162);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_126 = x_164;
goto block_156;
}
case 3:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_124);
x_165 = lean_ctor_get(x_119, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_119, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_119, 4);
lean_inc(x_167);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
lean_ctor_set(x_168, 2, x_167);
x_169 = lean_ctor_get(x_119, 5);
lean_inc(x_169);
x_170 = lean_ctor_get(x_119, 2);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_170, sizeof(void*)*2 + 3);
lean_dec(x_170);
x_172 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set_uint8(x_172, sizeof(void*)*2, x_171);
x_173 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_126 = x_173;
goto block_156;
}
case 4:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
lean_dec(x_124);
x_174 = lean_ctor_get(x_119, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_119, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_119, 4);
lean_inc(x_176);
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_176);
x_178 = lean_ctor_get(x_119, 2);
lean_inc(x_178);
x_179 = lean_ctor_get_uint8(x_178, sizeof(void*)*2 + 3);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_119, 5);
lean_inc(x_180);
x_181 = lean_box(1);
x_182 = 1;
x_183 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_183, 0, x_177);
lean_ctor_set(x_183, 1, x_180);
lean_ctor_set(x_183, 2, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*3, x_182);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
x_126 = x_184;
goto block_156;
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_119, 5);
lean_inc(x_185);
x_186 = lean_box(1);
x_187 = 0;
x_188 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_188, 0, x_177);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*3, x_187);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_126 = x_189;
goto block_156;
}
}
default: 
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint32_t x_196; uint32_t x_197; uint32_t x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
lean_dec(x_157);
x_190 = lean_ctor_get(x_119, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_119, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_119, 4);
lean_inc(x_192);
x_193 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
lean_ctor_set(x_193, 2, x_192);
x_194 = lean_ctor_get(x_119, 5);
lean_inc(x_194);
lean_inc(x_194);
x_195 = l_Lean_getMaxHeight(x_124, x_194);
x_196 = lean_unbox_uint32(x_195);
lean_dec(x_195);
x_197 = 1;
x_198 = x_196 + x_197;
x_199 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_199, 0, x_198);
x_200 = lean_ctor_get(x_119, 2);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_200, sizeof(void*)*2 + 3);
lean_dec(x_200);
if (x_201 == 0)
{
uint8_t x_202; lean_object* x_203; lean_object* x_204; 
x_202 = 1;
x_203 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_203, 0, x_193);
lean_ctor_set(x_203, 1, x_194);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set_uint8(x_203, sizeof(void*)*3, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_126 = x_204;
goto block_156;
}
else
{
uint8_t x_205; lean_object* x_206; lean_object* x_207; 
x_205 = 0;
x_206 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_206, 0, x_193);
lean_ctor_set(x_206, 1, x_194);
lean_ctor_set(x_206, 2, x_199);
lean_ctor_set_uint8(x_206, sizeof(void*)*3, x_205);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_126 = x_207;
goto block_156;
}
}
}
block_156:
{
lean_object* x_127; 
lean_inc(x_117);
lean_inc(x_3);
lean_inc(x_126);
x_127 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_126, x_3, x_4, x_5, x_6, x_117, x_8, x_123);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1;
lean_inc(x_119);
x_130 = lean_array_push(x_129, x_119);
x_131 = 0;
lean_inc(x_8);
lean_inc(x_117);
lean_inc(x_3);
x_132 = l_Lean_Elab_applyAttributesOf(x_130, x_131, x_3, x_4, x_5, x_6, x_117, x_8, x_128);
if (lean_obj_tag(x_132) == 0)
{
if (x_2 == 0)
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; 
lean_dec(x_126);
lean_dec(x_119);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = 1;
x_135 = l_Lean_Elab_applyAttributesOf(x_130, x_134, x_3, x_4, x_5, x_6, x_117, x_8, x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_130);
return x_135;
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
lean_dec(x_132);
x_137 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_119);
lean_dec(x_119);
if (x_137 == 0)
{
uint8_t x_138; lean_object* x_139; 
lean_dec(x_126);
x_138 = 1;
x_139 = l_Lean_Elab_applyAttributesOf(x_130, x_138, x_3, x_4, x_5, x_6, x_117, x_8, x_136);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_130);
return x_139;
}
else
{
lean_object* x_140; 
lean_inc(x_8);
lean_inc(x_117);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_140 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(x_126, x_3, x_4, x_5, x_6, x_117, x_8, x_136);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = 1;
x_143 = l_Lean_Elab_applyAttributesOf(x_130, x_142, x_3, x_4, x_5, x_6, x_117, x_8, x_141);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_130);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_130);
lean_dec(x_117);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_ctor_get(x_140, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_146 = x_140;
} else {
 lean_dec_ref(x_140);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_130);
lean_dec(x_126);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_132, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_132, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_150 = x_132;
} else {
 lean_dec_ref(x_132);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_126);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_127, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_127, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_154 = x_127;
} else {
 lean_dec_ref(x_127);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_117);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_208 = lean_ctor_get(x_118, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_118, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_210 = x_118;
} else {
 lean_dec_ref(x_118);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_addAndCompileUnsafe___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 4);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_ctor_get(x_6, 5);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_14);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 4);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_ctor_get(x_16, 5);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_1);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
x_2 = x_17;
x_3 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = l_Lean_Elab_instInhabitedPreDefinition;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_1);
x_14 = lean_array_to_list(lean_box(0), x_1);
x_15 = lean_box(0);
x_16 = l_List_mapTRAux___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_2, x_14, x_15);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 3);
x_20 = l_Lean_replaceRef(x_13, x_19);
lean_dec(x_19);
lean_dec(x_13);
lean_ctor_set(x_7, 3, x_20);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_17);
x_21 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_24 = l_Lean_Elab_applyAttributesOf(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 1;
x_29 = l_Lean_Elab_applyAttributesOf(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
return x_24;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_24, 0);
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_24);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
return x_21;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_21);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_7, 0);
x_53 = lean_ctor_get(x_7, 1);
x_54 = lean_ctor_get(x_7, 2);
x_55 = lean_ctor_get(x_7, 3);
x_56 = lean_ctor_get(x_7, 4);
x_57 = lean_ctor_get(x_7, 5);
x_58 = lean_ctor_get(x_7, 6);
x_59 = lean_ctor_get(x_7, 7);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_7);
x_60 = l_Lean_replaceRef(x_13, x_55);
lean_dec(x_55);
lean_dec(x_13);
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_54);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_56);
lean_ctor_set(x_61, 5, x_57);
lean_ctor_set(x_61, 6, x_58);
lean_ctor_set(x_61, 7, x_59);
lean_inc(x_61);
lean_inc(x_3);
lean_inc(x_17);
x_62 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_17, x_3, x_4, x_5, x_6, x_61, x_8, x_9);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = 0;
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_3);
x_65 = l_Lean_Elab_applyAttributesOf(x_1, x_64, x_3, x_4, x_5, x_6, x_61, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_67 = l_Lean_compileDecl___at_Lean_Elab_Term_evalExpr___spec__5(x_17, x_3, x_4, x_5, x_6, x_61, x_8, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = 1;
x_70 = l_Lean_Elab_applyAttributesOf(x_1, x_69, x_3, x_4, x_5, x_6, x_61, x_8, x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = lean_ctor_get(x_67, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_67, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_81 = x_67;
} else {
 lean_dec_ref(x_67);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_61);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_83 = lean_ctor_get(x_65, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_85 = x_65;
} else {
 lean_dec_ref(x_65);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_61);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_87 = lean_ctor_get(x_62, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_62, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_89 = x_62;
} else {
 lean_dec_ref(x_62);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_addAndCompileUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_List_mapTRAux___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_addAndCompileUnsafe(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
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
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_unsafe_rec");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_215; lean_object* x_216; size_t x_217; uint8_t x_218; 
x_6 = lean_ptr_addr(x_4);
x_7 = x_3 == 0 ? x_6 : x_6 % x_3;
x_215 = lean_ctor_get(x_5, 0);
lean_inc(x_215);
x_216 = lean_array_uget(x_215, x_7);
lean_dec(x_215);
x_217 = lean_ptr_addr(x_216);
lean_dec(x_216);
x_218 = x_217 == x_6;
if (x_218 == 0)
{
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_4, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_4, 1);
lean_inc(x_220);
x_221 = lean_unsigned_to_nat(0u);
x_222 = lean_nat_dec_lt(x_221, x_2);
if (x_222 == 0)
{
lean_object* x_223; 
lean_dec(x_220);
lean_dec(x_219);
x_223 = lean_box(0);
x_8 = x_223;
goto block_214;
}
else
{
uint8_t x_224; 
x_224 = lean_nat_dec_le(x_2, x_2);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_220);
lean_dec(x_219);
x_225 = lean_box(0);
x_8 = x_225;
goto block_214;
}
else
{
size_t x_226; size_t x_227; uint8_t x_228; 
x_226 = 0;
x_227 = lean_usize_of_nat(x_2);
x_228 = l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1(x_219, x_1, x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_220);
lean_dec(x_219);
x_229 = lean_box(0);
x_8 = x_229;
goto block_214;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_230 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1;
x_231 = lean_name_mk_string(x_219, x_230);
x_232 = l_Lean_mkConst(x_231, x_220);
x_233 = !lean_is_exclusive(x_5);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_5, 0);
x_235 = lean_ctor_get(x_5, 1);
x_236 = lean_array_uset(x_234, x_7, x_4);
lean_inc(x_232);
x_237 = lean_array_uset(x_235, x_7, x_232);
lean_ctor_set(x_5, 1, x_237);
lean_ctor_set(x_5, 0, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_232);
lean_ctor_set(x_238, 1, x_5);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_5, 0);
x_240 = lean_ctor_get(x_5, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_5);
x_241 = lean_array_uset(x_239, x_7, x_4);
lean_inc(x_232);
x_242 = lean_array_uset(x_240, x_7, x_232);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_232);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
}
else
{
lean_object* x_245; 
x_245 = lean_box(0);
x_8 = x_245;
goto block_214;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_4);
x_246 = lean_ctor_get(x_5, 1);
lean_inc(x_246);
x_247 = lean_array_uget(x_246, x_7);
lean_dec(x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_5);
return x_248;
}
block_214:
{
lean_dec(x_8);
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_9);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_9, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_10, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set_uint64(x_19, sizeof(void*)*2, x_11);
x_20 = lean_expr_update_app(x_19, x_13, x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
x_24 = lean_array_uset(x_22, x_7, x_4);
lean_inc(x_20);
x_25 = lean_array_uset(x_23, x_7, x_20);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_24);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_array_uset(x_26, x_7, x_4);
lean_inc(x_20);
x_29 = lean_array_uset(x_27, x_7, x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_15, 1, x_30);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set_uint64(x_33, sizeof(void*)*2, x_11);
x_34 = lean_expr_update_app(x_33, x_13, x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_37 = x_32;
} else {
 lean_dec_ref(x_32);
 x_37 = lean_box(0);
}
x_38 = lean_array_uset(x_35, x_7, x_4);
lean_inc(x_34);
x_39 = lean_array_uset(x_36, x_7, x_34);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_43);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_43, x_5);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_44);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_44, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_53 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set_uint64(x_53, sizeof(void*)*3, x_45);
x_54 = (uint8_t)((x_45 << 24) >> 61);
x_55 = lean_expr_update_lambda(x_53, x_54, x_47, x_51);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
x_59 = lean_array_uset(x_57, x_7, x_4);
lean_inc(x_55);
x_60 = lean_array_uset(x_58, x_7, x_55);
lean_ctor_set(x_52, 1, x_60);
lean_ctor_set(x_52, 0, x_59);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_array_uset(x_61, x_7, x_4);
lean_inc(x_55);
x_64 = lean_array_uset(x_62, x_7, x_55);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_49, 1, x_65);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_68 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_43);
lean_ctor_set(x_68, 2, x_44);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_45);
x_69 = (uint8_t)((x_45 << 24) >> 61);
x_70 = lean_expr_update_lambda(x_68, x_69, x_47, x_66);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
x_74 = lean_array_uset(x_71, x_7, x_4);
lean_inc(x_70);
x_75 = lean_array_uset(x_72, x_7, x_70);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
case 7:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_79);
x_82 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_79, x_5);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_80);
x_85 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_89, 0, x_78);
lean_ctor_set(x_89, 1, x_79);
lean_ctor_set(x_89, 2, x_80);
lean_ctor_set_uint64(x_89, sizeof(void*)*3, x_81);
x_90 = (uint8_t)((x_81 << 24) >> 61);
x_91 = lean_expr_update_forall(x_89, x_90, x_83, x_87);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
x_95 = lean_array_uset(x_93, x_7, x_4);
lean_inc(x_91);
x_96 = lean_array_uset(x_94, x_7, x_91);
lean_ctor_set(x_88, 1, x_96);
lean_ctor_set(x_88, 0, x_95);
lean_ctor_set(x_85, 0, x_91);
return x_85;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_array_uset(x_97, x_7, x_4);
lean_inc(x_91);
x_100 = lean_array_uset(x_98, x_7, x_91);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_85, 1, x_101);
lean_ctor_set(x_85, 0, x_91);
return x_85;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_102 = lean_ctor_get(x_85, 0);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_85);
x_104 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_104, 0, x_78);
lean_ctor_set(x_104, 1, x_79);
lean_ctor_set(x_104, 2, x_80);
lean_ctor_set_uint64(x_104, sizeof(void*)*3, x_81);
x_105 = (uint8_t)((x_81 << 24) >> 61);
x_106 = lean_expr_update_forall(x_104, x_105, x_83, x_102);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = lean_array_uset(x_107, x_7, x_4);
lean_inc(x_106);
x_111 = lean_array_uset(x_108, x_7, x_106);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
case 8:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint64_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_114 = lean_ctor_get(x_4, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_4, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_4, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_4, 3);
lean_inc(x_117);
x_118 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
lean_inc(x_115);
x_119 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_115, x_5);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_116);
x_122 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_116, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_117);
x_125 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_117, x_124);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
x_129 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_129, 0, x_114);
lean_ctor_set(x_129, 1, x_115);
lean_ctor_set(x_129, 2, x_116);
lean_ctor_set(x_129, 3, x_117);
lean_ctor_set_uint64(x_129, sizeof(void*)*4, x_118);
x_130 = lean_expr_update_let(x_129, x_120, x_123, x_127);
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
x_134 = lean_array_uset(x_132, x_7, x_4);
lean_inc(x_130);
x_135 = lean_array_uset(x_133, x_7, x_130);
lean_ctor_set(x_128, 1, x_135);
lean_ctor_set(x_128, 0, x_134);
lean_ctor_set(x_125, 0, x_130);
return x_125;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_128, 0);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_128);
x_138 = lean_array_uset(x_136, x_7, x_4);
lean_inc(x_130);
x_139 = lean_array_uset(x_137, x_7, x_130);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_125, 1, x_140);
lean_ctor_set(x_125, 0, x_130);
return x_125;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_125, 0);
x_142 = lean_ctor_get(x_125, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_125);
x_143 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_143, 0, x_114);
lean_ctor_set(x_143, 1, x_115);
lean_ctor_set(x_143, 2, x_116);
lean_ctor_set(x_143, 3, x_117);
lean_ctor_set_uint64(x_143, sizeof(void*)*4, x_118);
x_144 = lean_expr_update_let(x_143, x_120, x_123, x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = lean_array_uset(x_145, x_7, x_4);
lean_inc(x_144);
x_149 = lean_array_uset(x_146, x_7, x_144);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
case 10:
{
lean_object* x_152; lean_object* x_153; uint64_t x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_4, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_4, 1);
lean_inc(x_153);
x_154 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_inc(x_153);
x_155 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_153, x_5);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_159, 0, x_152);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set_uint64(x_159, sizeof(void*)*2, x_154);
x_160 = lean_expr_update_mdata(x_159, x_157);
x_161 = !lean_is_exclusive(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_158, 0);
x_163 = lean_ctor_get(x_158, 1);
x_164 = lean_array_uset(x_162, x_7, x_4);
lean_inc(x_160);
x_165 = lean_array_uset(x_163, x_7, x_160);
lean_ctor_set(x_158, 1, x_165);
lean_ctor_set(x_158, 0, x_164);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_array_uset(x_166, x_7, x_4);
lean_inc(x_160);
x_169 = lean_array_uset(x_167, x_7, x_160);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_155, 1, x_170);
lean_ctor_set(x_155, 0, x_160);
return x_155;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_171 = lean_ctor_get(x_155, 0);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_155);
x_173 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_173, 0, x_152);
lean_ctor_set(x_173, 1, x_153);
lean_ctor_set_uint64(x_173, sizeof(void*)*2, x_154);
x_174 = lean_expr_update_mdata(x_173, x_171);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
 x_177 = lean_box(0);
}
x_178 = lean_array_uset(x_175, x_7, x_4);
lean_inc(x_174);
x_179 = lean_array_uset(x_176, x_7, x_174);
if (lean_is_scalar(x_177)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_177;
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_174);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
case 11:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint64_t x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_4, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_4, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_4, 2);
lean_inc(x_184);
x_185 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_184);
x_186 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_184, x_5);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = lean_ctor_get(x_186, 1);
x_190 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_190, 0, x_182);
lean_ctor_set(x_190, 1, x_183);
lean_ctor_set(x_190, 2, x_184);
lean_ctor_set_uint64(x_190, sizeof(void*)*3, x_185);
x_191 = lean_expr_update_proj(x_190, x_188);
x_192 = !lean_is_exclusive(x_189);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_189, 0);
x_194 = lean_ctor_get(x_189, 1);
x_195 = lean_array_uset(x_193, x_7, x_4);
lean_inc(x_191);
x_196 = lean_array_uset(x_194, x_7, x_191);
lean_ctor_set(x_189, 1, x_196);
lean_ctor_set(x_189, 0, x_195);
lean_ctor_set(x_186, 0, x_191);
return x_186;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_189, 0);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_189);
x_199 = lean_array_uset(x_197, x_7, x_4);
lean_inc(x_191);
x_200 = lean_array_uset(x_198, x_7, x_191);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_186, 1, x_201);
lean_ctor_set(x_186, 0, x_191);
return x_186;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_202 = lean_ctor_get(x_186, 0);
x_203 = lean_ctor_get(x_186, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_186);
x_204 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_204, 0, x_182);
lean_ctor_set(x_204, 1, x_183);
lean_ctor_set(x_204, 2, x_184);
lean_ctor_set_uint64(x_204, sizeof(void*)*3, x_185);
x_205 = lean_expr_update_proj(x_204, x_202);
x_206 = lean_ctor_get(x_203, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_208 = x_203;
} else {
 lean_dec_ref(x_203);
 x_208 = lean_box(0);
}
x_209 = lean_array_uset(x_206, x_7, x_4);
lean_inc(x_205);
x_210 = lean_array_uset(x_207, x_7, x_205);
if (lean_is_scalar(x_208)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_208;
}
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
default: 
{
lean_object* x_213; 
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_4);
lean_ctor_set(x_213, 1, x_5);
return x_213;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 2;
x_5 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = x_5;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_ctor_get(x_11, 3);
x_14 = lean_ctor_get(x_11, 5);
x_15 = lean_ctor_get(x_11, 2);
lean_dec(x_15);
x_16 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1;
x_17 = lean_name_mk_string(x_13, x_16);
x_18 = 8192;
x_19 = l_Lean_Expr_ReplaceImpl_initCache;
x_20 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_18, x_14, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1;
lean_ctor_set(x_11, 5, x_21);
lean_ctor_set(x_11, 3, x_17);
lean_ctor_set(x_11, 2, x_22);
x_23 = 1;
x_24 = x_4 + x_23;
x_25 = x_11;
x_26 = lean_array_uset(x_10, x_4, x_25);
x_4 = x_24;
x_5 = x_26;
goto _start;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
x_30 = lean_ctor_get(x_11, 1);
x_31 = lean_ctor_get(x_11, 3);
x_32 = lean_ctor_get(x_11, 4);
x_33 = lean_ctor_get(x_11, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_dec(x_11);
x_34 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1;
x_35 = lean_name_mk_string(x_31, x_34);
x_36 = 8192;
x_37 = l_Lean_Expr_ReplaceImpl_initCache;
x_38 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_36, x_33, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1;
x_41 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_35);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*6, x_29);
x_42 = 1;
x_43 = x_4 + x_42;
x_44 = x_41;
x_45 = lean_array_uset(x_10, x_4, x_44);
x_4 = x_43;
x_5 = x_45;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_5);
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
x_9 = x_2 + x_8;
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
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_19; uint8_t x_20; 
x_9 = lean_array_get_size(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_9);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
x_10 = x_21;
goto block_18;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_9, x_9);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
x_10 = x_23;
goto block_18;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_9);
x_26 = l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__4(x_1, x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_10 = x_27;
goto block_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
block_18:
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_dec(x_10);
x_11 = lean_usize_of_nat(x_9);
x_12 = 0;
lean_inc(x_1);
x_13 = x_1;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3(x_1, x_9, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_1);
x_15 = x_14;
x_16 = 2;
x_17 = l_Lean_Elab_addAndCompileUnsafe(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__4(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_SCC(lean_object*);
lean_object* initialize_Lean_Meta_AbstractNestedProofs(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_DefView(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SCC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractNestedProofs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_MkInhabitant(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedPreDefinition___closed__1 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__1);
l_Lean_Elab_instInhabitedPreDefinition___closed__2 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__2);
l_Lean_Elab_instInhabitedPreDefinition___closed__3 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__3();
l_Lean_Elab_instInhabitedPreDefinition___closed__4 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__4();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__4);
l_Lean_Elab_instInhabitedPreDefinition___closed__5 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__5();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__5);
l_Lean_Elab_instInhabitedPreDefinition = _init_l_Lean_Elab_instInhabitedPreDefinition();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition);
l_Lean_Elab_instantiateMVarsAtPreDecls___boxed__const__1 = _init_l_Lean_Elab_instantiateMVarsAtPreDecls___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_instantiateMVarsAtPreDecls___boxed__const__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___boxed__const__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_levelMVarToParamPreDeclsAux___boxed__const__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___closed__1);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
