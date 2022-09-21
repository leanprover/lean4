// Lean compiler output
// Module: Lean.Compiler.LCNF.CSE
// Imports: Init Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.PassManager
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Code_cse_go___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__4;
static lean_object* l_Lean_Compiler_LCNF_cse___closed__2;
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_toExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_State_map___default___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_Code_cse_go___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Code_cse_go___spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Std_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_State_subst___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Code_cse_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_CSE_State_map___default___closed__1;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_Code_cse_go___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__3;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__1;
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_State_subst___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_State_map___default;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_State_map___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_State_map___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_CSE_State_map___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_State_map___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_State_map___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_State_subst___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_State_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_CSE_State_subst___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_get(x_1, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2___rarg), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
x_2 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2___rarg), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_apply_1(x_1, x_13);
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_2, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_apply_1(x_1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_st_ref_set(x_2, x_25, x_11);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_st_ref_get(x_1, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_CSE_getSubst(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_eqv(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_eqv(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Expr_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_3, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_23, x_1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_st_ref_set(x_3, x_26, x_12);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CSE_addEntry(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_2);
x_13 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_2, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_12);
x_23 = lean_st_ref_set(x_2, x_19, x_20);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_14);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_st_ref_set(x_2, x_29, x_20);
lean_dec(x_2);
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
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_st_ref_get(x_5, x_35);
lean_dec(x_5);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_take(x_2, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
lean_ctor_set(x_39, 0, x_12);
x_43 = lean_st_ref_set(x_2, x_39, x_40);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_34);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_st_ref_set(x_2, x_49, x_40);
lean_dec(x_2);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
 lean_ctor_set_tag(x_53, 1);
}
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_withNewScope___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Compiler_LCNF_eraseLetDecl(x_1, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_st_ref_get(x_6, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Expr_fvar___override(x_2);
x_19 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_17, x_10, x_18);
lean_ctor_set(x_14, 1, x_19);
x_20 = lean_st_ref_set(x_3, x_14, x_15);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = l_Lean_Expr_fvar___override(x_2);
x_30 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_28, x_10, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_st_ref_set(x_3, x_31, x_15);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CSE_replaceLet(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = 1;
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_eraseFunDecl(x_1, x_8, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_st_ref_get(x_6, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Expr_fvar___override(x_2);
x_20 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_18, x_11, x_19);
lean_ctor_set(x_15, 1, x_20);
x_21 = lean_st_ref_set(x_3, x_15, x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l_Lean_Expr_fvar___override(x_2);
x_31 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_29, x_11, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_st_ref_set(x_3, x_32, x_16);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CSE_replaceFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_1, x_8);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_2, x_15, x_4, x_5, x_6, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_13 = lean_apply_6(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = lean_array_fset(x_3, x_2, x_14);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_21;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
x_2 = x_24;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__4(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2___boxed), 7, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__3(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_14, x_7);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(x_14, x_16, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
x_30 = lean_st_ref_get(x_5, x_19);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_2, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l_Lean_Compiler_LCNF_Code_cse_go(x_20, x_2, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_5, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_2, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 0);
lean_dec(x_45);
lean_ctor_set(x_42, 0, x_35);
x_46 = lean_st_ref_set(x_2, x_42, x_43);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_37);
x_21 = x_46;
goto block_29;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_37);
lean_ctor_set(x_50, 1, x_49);
x_21 = x_50;
goto block_29;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_35);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_st_ref_set(x_2, x_52, x_43);
lean_dec(x_2);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_37);
lean_ctor_set(x_56, 1, x_54);
x_21 = x_56;
goto block_29;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_36, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_36, 1);
lean_inc(x_58);
lean_dec(x_36);
x_59 = lean_st_ref_get(x_5, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_take(x_2, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
lean_ctor_set(x_62, 0, x_35);
x_66 = lean_st_ref_set(x_2, x_62, x_63);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_57);
x_21 = x_66;
goto block_29;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_69);
x_21 = x_70;
goto block_29;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_35);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_st_ref_set(x_2, x_72, x_63);
lean_dec(x_2);
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
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_74);
x_21 = x_76;
goto block_29;
}
}
block_29:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_15, x_18, x_22, x_3, x_4, x_5, x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_17);
if (x_77 == 0)
{
return x_17;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_17, 0);
x_79 = lean_ctor_get(x_17, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_17);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_14, x_1, x_8);
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
x_17 = lean_st_ref_get(x_6, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_22, x_1, x_16);
x_24 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(x_2, x_15, x_23, x_4, x_5, x_6, x_21);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_eqv(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_Code_cse_go___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Code_cse_go___spec__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_1, x_2);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_17, x_1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_13 = lean_apply_6(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = lean_array_fset(x_3, x_2, x_14);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_21;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
x_2 = x_24;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__8(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Code_cse_go___spec__6___boxed), 7, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__7(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_13 = lean_apply_6(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = lean_array_fset(x_3, x_2, x_14);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_21;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
x_2 = x_24;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__10(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_36; lean_object* x_37; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_36 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(x_36, x_7, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_5);
lean_inc(x_2);
x_40 = l_Lean_Compiler_LCNF_Code_cse_go(x_8, x_2, x_3, x_4, x_5, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(x_1, x_38, x_41);
x_44 = lean_st_ref_get(x_5, x_42);
lean_dec(x_5);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_take(x_2, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
lean_ctor_set(x_47, 0, x_14);
x_51 = lean_st_ref_set(x_2, x_47, x_48);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_43);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_st_ref_set(x_2, x_57, x_48);
lean_dec(x_2);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_43);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_38);
lean_dec(x_1);
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_40, 1);
lean_inc(x_63);
lean_dec(x_40);
x_15 = x_62;
x_16 = x_63;
goto block_35;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
lean_dec(x_37);
x_15 = x_64;
x_16 = x_65;
goto block_35;
}
block_35:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_st_ref_get(x_5, x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_2, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
lean_ctor_set(x_20, 0, x_14);
x_24 = lean_st_ref_set(x_2, x_20, x_21);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_15);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_st_ref_set(x_2, x_30, x_21);
lean_dec(x_2);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_st_ref_get(x_5, x_6);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_get(x_2, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_5);
lean_inc(x_2);
x_73 = l_Lean_Compiler_LCNF_Code_cse_go(x_66, x_2, x_3, x_4, x_5, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_74);
x_77 = lean_st_ref_get(x_5, x_75);
lean_dec(x_5);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_take(x_2, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_80, 0);
lean_dec(x_83);
lean_ctor_set(x_80, 0, x_72);
x_84 = lean_st_ref_set(x_2, x_80, x_81);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_76);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_72);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_st_ref_set(x_2, x_90, x_81);
lean_dec(x_2);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_76);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_1);
x_95 = lean_ctor_get(x_73, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_73, 1);
lean_inc(x_96);
lean_dec(x_73);
x_97 = lean_st_ref_get(x_5, x_96);
lean_dec(x_5);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_st_ref_take(x_2, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = !lean_is_exclusive(x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_100, 0);
lean_dec(x_103);
lean_ctor_set(x_100, 0, x_72);
x_104 = lean_st_ref_set(x_2, x_100, x_101);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_104, 0);
lean_dec(x_106);
lean_ctor_set_tag(x_104, 1);
lean_ctor_set(x_104, 0, x_95);
return x_104;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_95);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_dec(x_100);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_72);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_st_ref_set(x_2, x_110, x_101);
lean_dec(x_2);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_95);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_cse_go___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 0;
lean_inc(x_7);
x_10 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1(x_9, x_7, x_2, x_3, x_4, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_11, 3);
lean_inc(x_19);
lean_inc(x_19);
x_20 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_Code_cse_go___spec__2(x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
x_22 = lean_st_ref_get(x_5, x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_take(x_2, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_28, x_19, x_21);
lean_ctor_set(x_25, 0, x_29);
x_30 = lean_st_ref_set(x_2, x_25, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_8);
x_32 = l_Lean_Compiler_LCNF_Code_cse_go(x_8, x_2, x_3, x_4, x_5, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; size_t x_35; size_t x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_36 = lean_ptr_addr(x_34);
x_37 = lean_usize_dec_eq(x_35, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_7);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_1, 0);
lean_dec(x_40);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_11);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
else
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_32, 0, x_41);
return x_32;
}
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_43 = lean_ptr_addr(x_11);
x_44 = lean_usize_dec_eq(x_42, x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_1, 1);
lean_dec(x_46);
x_47 = lean_ctor_get(x_1, 0);
lean_dec(x_47);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_11);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
else
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_34);
lean_ctor_set(x_32, 0, x_48);
return x_32;
}
}
else
{
lean_dec(x_34);
lean_dec(x_11);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_32, 0);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_32);
x_51 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_52 = lean_ptr_addr(x_49);
x_53 = lean_usize_dec_eq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_7);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_54 = x_1;
} else {
 lean_dec_ref(x_1);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_11);
lean_ctor_set(x_55, 1, x_49);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
else
{
size_t x_57; size_t x_58; uint8_t x_59; 
x_57 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_58 = lean_ptr_addr(x_11);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_60 = x_1;
} else {
 lean_dec_ref(x_1);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_49);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_50);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_49);
lean_dec(x_11);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_50);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
return x_32;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_25, 0);
x_69 = lean_ctor_get(x_25, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_25);
x_70 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_68, x_19, x_21);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_st_ref_set(x_2, x_71, x_26);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
lean_inc(x_8);
x_74 = l_Lean_Compiler_LCNF_Code_cse_go(x_8, x_2, x_3, x_4, x_5, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_79 = lean_ptr_addr(x_75);
x_80 = lean_usize_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_7);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_81 = x_1;
} else {
 lean_dec_ref(x_1);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_75);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_77;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
return x_83;
}
else
{
size_t x_84; size_t x_85; uint8_t x_86; 
x_84 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_85 = lean_ptr_addr(x_11);
x_86 = lean_usize_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_87 = x_1;
} else {
 lean_dec_ref(x_1);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_11);
lean_ctor_set(x_88, 1, x_75);
if (lean_is_scalar(x_77)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_77;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_76);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_11);
if (lean_is_scalar(x_77)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_77;
}
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_76);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_91 = lean_ctor_get(x_74, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_93 = x_74;
} else {
 lean_dec_ref(x_74);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_1);
x_95 = lean_ctor_get(x_20, 0);
lean_inc(x_95);
lean_dec(x_20);
x_96 = l_Lean_Compiler_LCNF_CSE_replaceLet(x_11, x_95, x_2, x_3, x_4, x_5, x_17);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_1 = x_8;
x_6 = x_97;
goto _start;
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_1, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_1, 1);
lean_inc(x_100);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_99);
x_101 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_99, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Compiler_LCNF_Code_cse_go___closed__1;
lean_inc(x_102);
x_105 = l_Lean_Compiler_LCNF_FunDeclCore_toExpr(x_102, x_104);
x_106 = lean_st_ref_get(x_5, x_103);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_get(x_2, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_105);
x_112 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_Code_cse_go___spec__2(x_111, x_105);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_113 = lean_ctor_get(x_102, 0);
lean_inc(x_113);
x_114 = lean_st_ref_get(x_5, x_110);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_st_ref_take(x_2, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_117, 0);
x_121 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_120, x_105, x_113);
lean_ctor_set(x_117, 0, x_121);
x_122 = lean_st_ref_set(x_2, x_117, x_118);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
lean_inc(x_100);
x_124 = l_Lean_Compiler_LCNF_Code_cse_go(x_100, x_2, x_3, x_4, x_5, x_123);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; size_t x_127; size_t x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_128 = lean_ptr_addr(x_126);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
uint8_t x_130; 
lean_dec(x_99);
x_130 = !lean_is_exclusive(x_1);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_1, 1);
lean_dec(x_131);
x_132 = lean_ctor_get(x_1, 0);
lean_dec(x_132);
lean_ctor_set(x_1, 1, x_126);
lean_ctor_set(x_1, 0, x_102);
lean_ctor_set(x_124, 0, x_1);
return x_124;
}
else
{
lean_object* x_133; 
lean_dec(x_1);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_102);
lean_ctor_set(x_133, 1, x_126);
lean_ctor_set(x_124, 0, x_133);
return x_124;
}
}
else
{
size_t x_134; size_t x_135; uint8_t x_136; 
x_134 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_135 = lean_ptr_addr(x_102);
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
lean_ctor_set(x_1, 0, x_102);
lean_ctor_set(x_124, 0, x_1);
return x_124;
}
else
{
lean_object* x_140; 
lean_dec(x_1);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_102);
lean_ctor_set(x_140, 1, x_126);
lean_ctor_set(x_124, 0, x_140);
return x_124;
}
}
else
{
lean_dec(x_126);
lean_dec(x_102);
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
x_143 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_144 = lean_ptr_addr(x_141);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_99);
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
lean_ctor_set(x_147, 0, x_102);
lean_ctor_set(x_147, 1, x_141);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_142);
return x_148;
}
else
{
size_t x_149; size_t x_150; uint8_t x_151; 
x_149 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_150 = lean_ptr_addr(x_102);
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
lean_ctor_set(x_153, 0, x_102);
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
lean_dec(x_102);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_1);
lean_ctor_set(x_155, 1, x_142);
return x_155;
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_124);
if (x_156 == 0)
{
return x_124;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_124, 0);
x_158 = lean_ctor_get(x_124, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_124);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_117, 0);
x_161 = lean_ctor_get(x_117, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_117);
x_162 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_160, x_105, x_113);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_st_ref_set(x_2, x_163, x_118);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
lean_inc(x_100);
x_166 = l_Lean_Compiler_LCNF_Code_cse_go(x_100, x_2, x_3, x_4, x_5, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; size_t x_170; size_t x_171; uint8_t x_172; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_171 = lean_ptr_addr(x_167);
x_172 = lean_usize_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_99);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_173 = x_1;
} else {
 lean_dec_ref(x_1);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_102);
lean_ctor_set(x_174, 1, x_167);
if (lean_is_scalar(x_169)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_169;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_168);
return x_175;
}
else
{
size_t x_176; size_t x_177; uint8_t x_178; 
x_176 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_177 = lean_ptr_addr(x_102);
x_178 = lean_usize_dec_eq(x_176, x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_179 = x_1;
} else {
 lean_dec_ref(x_1);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_102);
lean_ctor_set(x_180, 1, x_167);
if (lean_is_scalar(x_169)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_169;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_168);
return x_181;
}
else
{
lean_object* x_182; 
lean_dec(x_167);
lean_dec(x_102);
if (lean_is_scalar(x_169)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_169;
}
lean_ctor_set(x_182, 0, x_1);
lean_ctor_set(x_182, 1, x_168);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_102);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
x_183 = lean_ctor_get(x_166, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_166, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_185 = x_166;
} else {
 lean_dec_ref(x_166);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_105);
lean_dec(x_99);
lean_dec(x_1);
x_187 = lean_ctor_get(x_112, 0);
lean_inc(x_187);
lean_dec(x_112);
x_188 = l_Lean_Compiler_LCNF_CSE_replaceFun(x_102, x_187, x_2, x_3, x_4, x_5, x_110);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_1 = x_100;
x_6 = x_189;
goto _start;
}
}
else
{
uint8_t x_191; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_101);
if (x_191 == 0)
{
return x_101;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_101, 0);
x_193 = lean_ctor_get(x_101, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_101);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
case 2:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_1, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_1, 1);
lean_inc(x_196);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_195);
x_197 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_195, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
lean_inc(x_196);
x_200 = l_Lean_Compiler_LCNF_Code_cse_go(x_196, x_2, x_3, x_4, x_5, x_199);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; size_t x_203; size_t x_204; uint8_t x_205; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ptr_addr(x_196);
lean_dec(x_196);
x_204 = lean_ptr_addr(x_202);
x_205 = lean_usize_dec_eq(x_203, x_204);
if (x_205 == 0)
{
uint8_t x_206; 
lean_dec(x_195);
x_206 = !lean_is_exclusive(x_1);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_1, 1);
lean_dec(x_207);
x_208 = lean_ctor_get(x_1, 0);
lean_dec(x_208);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set(x_200, 0, x_1);
return x_200;
}
else
{
lean_object* x_209; 
lean_dec(x_1);
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_198);
lean_ctor_set(x_209, 1, x_202);
lean_ctor_set(x_200, 0, x_209);
return x_200;
}
}
else
{
size_t x_210; size_t x_211; uint8_t x_212; 
x_210 = lean_ptr_addr(x_195);
lean_dec(x_195);
x_211 = lean_ptr_addr(x_198);
x_212 = lean_usize_dec_eq(x_210, x_211);
if (x_212 == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_1);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_1, 1);
lean_dec(x_214);
x_215 = lean_ctor_get(x_1, 0);
lean_dec(x_215);
lean_ctor_set(x_1, 1, x_202);
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set(x_200, 0, x_1);
return x_200;
}
else
{
lean_object* x_216; 
lean_dec(x_1);
x_216 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_216, 0, x_198);
lean_ctor_set(x_216, 1, x_202);
lean_ctor_set(x_200, 0, x_216);
return x_200;
}
}
else
{
lean_dec(x_202);
lean_dec(x_198);
lean_ctor_set(x_200, 0, x_1);
return x_200;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; size_t x_219; size_t x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_200, 0);
x_218 = lean_ctor_get(x_200, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_200);
x_219 = lean_ptr_addr(x_196);
lean_dec(x_196);
x_220 = lean_ptr_addr(x_217);
x_221 = lean_usize_dec_eq(x_219, x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_195);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_222 = x_1;
} else {
 lean_dec_ref(x_1);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(2, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_198);
lean_ctor_set(x_223, 1, x_217);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_218);
return x_224;
}
else
{
size_t x_225; size_t x_226; uint8_t x_227; 
x_225 = lean_ptr_addr(x_195);
lean_dec(x_195);
x_226 = lean_ptr_addr(x_198);
x_227 = lean_usize_dec_eq(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_228 = x_1;
} else {
 lean_dec_ref(x_1);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(2, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_198);
lean_ctor_set(x_229, 1, x_217);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_218);
return x_230;
}
else
{
lean_object* x_231; 
lean_dec(x_217);
lean_dec(x_198);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_1);
lean_ctor_set(x_231, 1, x_218);
return x_231;
}
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_1);
x_232 = !lean_is_exclusive(x_200);
if (x_232 == 0)
{
return x_200;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_200, 0);
x_234 = lean_ctor_get(x_200, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_200);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_197);
if (x_236 == 0)
{
return x_197;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_197, 0);
x_238 = lean_ctor_get(x_197, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_197);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
case 3:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; 
x_240 = lean_ctor_get(x_1, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_1, 1);
lean_inc(x_241);
x_242 = lean_st_ref_get(x_5, x_6);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = lean_st_ref_get(x_2, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = 0;
lean_inc(x_240);
x_249 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_247, x_240, x_248);
lean_inc(x_241);
x_250 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5(x_248, x_241, x_2, x_3, x_4, x_5, x_246);
if (lean_obj_tag(x_250) == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; uint8_t x_253; 
x_252 = lean_ctor_get(x_250, 0);
x_253 = lean_name_eq(x_240, x_249);
lean_dec(x_240);
if (x_253 == 0)
{
uint8_t x_254; 
lean_dec(x_241);
x_254 = !lean_is_exclusive(x_1);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_1, 1);
lean_dec(x_255);
x_256 = lean_ctor_get(x_1, 0);
lean_dec(x_256);
lean_ctor_set(x_1, 1, x_252);
lean_ctor_set(x_1, 0, x_249);
lean_ctor_set(x_250, 0, x_1);
return x_250;
}
else
{
lean_object* x_257; 
lean_dec(x_1);
x_257 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_257, 0, x_249);
lean_ctor_set(x_257, 1, x_252);
lean_ctor_set(x_250, 0, x_257);
return x_250;
}
}
else
{
size_t x_258; size_t x_259; uint8_t x_260; 
x_258 = lean_ptr_addr(x_241);
lean_dec(x_241);
x_259 = lean_ptr_addr(x_252);
x_260 = lean_usize_dec_eq(x_258, x_259);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_1);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_1, 1);
lean_dec(x_262);
x_263 = lean_ctor_get(x_1, 0);
lean_dec(x_263);
lean_ctor_set(x_1, 1, x_252);
lean_ctor_set(x_1, 0, x_249);
lean_ctor_set(x_250, 0, x_1);
return x_250;
}
else
{
lean_object* x_264; 
lean_dec(x_1);
x_264 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_264, 0, x_249);
lean_ctor_set(x_264, 1, x_252);
lean_ctor_set(x_250, 0, x_264);
return x_250;
}
}
else
{
lean_dec(x_252);
lean_dec(x_249);
lean_ctor_set(x_250, 0, x_1);
return x_250;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_265 = lean_ctor_get(x_250, 0);
x_266 = lean_ctor_get(x_250, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_250);
x_267 = lean_name_eq(x_240, x_249);
lean_dec(x_240);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_241);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_268 = x_1;
} else {
 lean_dec_ref(x_1);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(3, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_249);
lean_ctor_set(x_269, 1, x_265);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_266);
return x_270;
}
else
{
size_t x_271; size_t x_272; uint8_t x_273; 
x_271 = lean_ptr_addr(x_241);
lean_dec(x_241);
x_272 = lean_ptr_addr(x_265);
x_273 = lean_usize_dec_eq(x_271, x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_274 = x_1;
} else {
 lean_dec_ref(x_1);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(3, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_249);
lean_ctor_set(x_275, 1, x_265);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_266);
return x_276;
}
else
{
lean_object* x_277; 
lean_dec(x_265);
lean_dec(x_249);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_1);
lean_ctor_set(x_277, 1, x_266);
return x_277;
}
}
}
}
else
{
uint8_t x_278; 
lean_dec(x_249);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_1);
x_278 = !lean_is_exclusive(x_250);
if (x_278 == 0)
{
return x_250;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_250, 0);
x_280 = lean_ctor_get(x_250, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_250);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
case 4:
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_1, 0);
lean_inc(x_282);
x_283 = !lean_is_exclusive(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_284 = lean_ctor_get(x_282, 0);
x_285 = lean_ctor_get(x_282, 1);
x_286 = lean_ctor_get(x_282, 2);
x_287 = lean_ctor_get(x_282, 3);
x_288 = lean_st_ref_get(x_5, x_6);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
x_290 = lean_st_ref_get(x_2, x_289);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = 0;
lean_inc(x_286);
x_295 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_293, x_286, x_294);
x_296 = lean_st_ref_get(x_5, x_292);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_298 = lean_st_ref_get(x_2, x_297);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
lean_inc(x_285);
x_302 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_301, x_294, x_285);
x_303 = l_Lean_Compiler_LCNF_Code_cse_go___closed__2;
lean_inc(x_287);
x_304 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__9(x_287, x_303, x_2, x_3, x_4, x_5, x_300);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; size_t x_307; size_t x_308; uint8_t x_309; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = lean_ptr_addr(x_287);
lean_dec(x_287);
x_308 = lean_ptr_addr(x_306);
x_309 = lean_usize_dec_eq(x_307, x_308);
if (x_309 == 0)
{
uint8_t x_310; 
lean_dec(x_286);
lean_dec(x_285);
x_310 = !lean_is_exclusive(x_1);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_1, 0);
lean_dec(x_311);
lean_ctor_set(x_282, 3, x_306);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
lean_ctor_set(x_304, 0, x_1);
return x_304;
}
else
{
lean_object* x_312; 
lean_dec(x_1);
lean_ctor_set(x_282, 3, x_306);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
x_312 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_312, 0, x_282);
lean_ctor_set(x_304, 0, x_312);
return x_304;
}
}
else
{
size_t x_313; size_t x_314; uint8_t x_315; 
x_313 = lean_ptr_addr(x_285);
lean_dec(x_285);
x_314 = lean_ptr_addr(x_302);
x_315 = lean_usize_dec_eq(x_313, x_314);
if (x_315 == 0)
{
uint8_t x_316; 
lean_dec(x_286);
x_316 = !lean_is_exclusive(x_1);
if (x_316 == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_1, 0);
lean_dec(x_317);
lean_ctor_set(x_282, 3, x_306);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
lean_ctor_set(x_304, 0, x_1);
return x_304;
}
else
{
lean_object* x_318; 
lean_dec(x_1);
lean_ctor_set(x_282, 3, x_306);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
x_318 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_318, 0, x_282);
lean_ctor_set(x_304, 0, x_318);
return x_304;
}
}
else
{
uint8_t x_319; 
x_319 = lean_name_eq(x_286, x_295);
lean_dec(x_286);
if (x_319 == 0)
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_1);
if (x_320 == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_1, 0);
lean_dec(x_321);
lean_ctor_set(x_282, 3, x_306);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
lean_ctor_set(x_304, 0, x_1);
return x_304;
}
else
{
lean_object* x_322; 
lean_dec(x_1);
lean_ctor_set(x_282, 3, x_306);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
x_322 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_322, 0, x_282);
lean_ctor_set(x_304, 0, x_322);
return x_304;
}
}
else
{
lean_dec(x_306);
lean_dec(x_302);
lean_dec(x_295);
lean_free_object(x_282);
lean_dec(x_284);
lean_ctor_set(x_304, 0, x_1);
return x_304;
}
}
}
}
else
{
lean_object* x_323; lean_object* x_324; size_t x_325; size_t x_326; uint8_t x_327; 
x_323 = lean_ctor_get(x_304, 0);
x_324 = lean_ctor_get(x_304, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_304);
x_325 = lean_ptr_addr(x_287);
lean_dec(x_287);
x_326 = lean_ptr_addr(x_323);
x_327 = lean_usize_dec_eq(x_325, x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_286);
lean_dec(x_285);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_328 = x_1;
} else {
 lean_dec_ref(x_1);
 x_328 = lean_box(0);
}
lean_ctor_set(x_282, 3, x_323);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(4, 1, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_282);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_324);
return x_330;
}
else
{
size_t x_331; size_t x_332; uint8_t x_333; 
x_331 = lean_ptr_addr(x_285);
lean_dec(x_285);
x_332 = lean_ptr_addr(x_302);
x_333 = lean_usize_dec_eq(x_331, x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_286);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_334 = x_1;
} else {
 lean_dec_ref(x_1);
 x_334 = lean_box(0);
}
lean_ctor_set(x_282, 3, x_323);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(4, 1, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_282);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_324);
return x_336;
}
else
{
uint8_t x_337; 
x_337 = lean_name_eq(x_286, x_295);
lean_dec(x_286);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_338 = x_1;
} else {
 lean_dec_ref(x_1);
 x_338 = lean_box(0);
}
lean_ctor_set(x_282, 3, x_323);
lean_ctor_set(x_282, 2, x_295);
lean_ctor_set(x_282, 1, x_302);
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(4, 1, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_282);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_324);
return x_340;
}
else
{
lean_object* x_341; 
lean_dec(x_323);
lean_dec(x_302);
lean_dec(x_295);
lean_free_object(x_282);
lean_dec(x_284);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_1);
lean_ctor_set(x_341, 1, x_324);
return x_341;
}
}
}
}
}
else
{
uint8_t x_342; 
lean_dec(x_302);
lean_dec(x_295);
lean_free_object(x_282);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_1);
x_342 = !lean_is_exclusive(x_304);
if (x_342 == 0)
{
return x_304;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_304, 0);
x_344 = lean_ctor_get(x_304, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_304);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_346 = lean_ctor_get(x_282, 0);
x_347 = lean_ctor_get(x_282, 1);
x_348 = lean_ctor_get(x_282, 2);
x_349 = lean_ctor_get(x_282, 3);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_282);
x_350 = lean_st_ref_get(x_5, x_6);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
lean_dec(x_350);
x_352 = lean_st_ref_get(x_2, x_351);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = 0;
lean_inc(x_348);
x_357 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_355, x_348, x_356);
x_358 = lean_st_ref_get(x_5, x_354);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
lean_dec(x_358);
x_360 = lean_st_ref_get(x_2, x_359);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
lean_inc(x_347);
x_364 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_363, x_356, x_347);
x_365 = l_Lean_Compiler_LCNF_Code_cse_go___closed__2;
lean_inc(x_349);
x_366 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__9(x_349, x_365, x_2, x_3, x_4, x_5, x_362);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; size_t x_370; size_t x_371; uint8_t x_372; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
x_370 = lean_ptr_addr(x_349);
lean_dec(x_349);
x_371 = lean_ptr_addr(x_367);
x_372 = lean_usize_dec_eq(x_370, x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_348);
lean_dec(x_347);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_373 = x_1;
} else {
 lean_dec_ref(x_1);
 x_373 = lean_box(0);
}
x_374 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_374, 0, x_346);
lean_ctor_set(x_374, 1, x_364);
lean_ctor_set(x_374, 2, x_357);
lean_ctor_set(x_374, 3, x_367);
if (lean_is_scalar(x_373)) {
 x_375 = lean_alloc_ctor(4, 1, 0);
} else {
 x_375 = x_373;
}
lean_ctor_set(x_375, 0, x_374);
if (lean_is_scalar(x_369)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_369;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_368);
return x_376;
}
else
{
size_t x_377; size_t x_378; uint8_t x_379; 
x_377 = lean_ptr_addr(x_347);
lean_dec(x_347);
x_378 = lean_ptr_addr(x_364);
x_379 = lean_usize_dec_eq(x_377, x_378);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_348);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_380 = x_1;
} else {
 lean_dec_ref(x_1);
 x_380 = lean_box(0);
}
x_381 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_381, 0, x_346);
lean_ctor_set(x_381, 1, x_364);
lean_ctor_set(x_381, 2, x_357);
lean_ctor_set(x_381, 3, x_367);
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(4, 1, 0);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_381);
if (lean_is_scalar(x_369)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_369;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_368);
return x_383;
}
else
{
uint8_t x_384; 
x_384 = lean_name_eq(x_348, x_357);
lean_dec(x_348);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_385 = x_1;
} else {
 lean_dec_ref(x_1);
 x_385 = lean_box(0);
}
x_386 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_386, 0, x_346);
lean_ctor_set(x_386, 1, x_364);
lean_ctor_set(x_386, 2, x_357);
lean_ctor_set(x_386, 3, x_367);
if (lean_is_scalar(x_385)) {
 x_387 = lean_alloc_ctor(4, 1, 0);
} else {
 x_387 = x_385;
}
lean_ctor_set(x_387, 0, x_386);
if (lean_is_scalar(x_369)) {
 x_388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_388 = x_369;
}
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_368);
return x_388;
}
else
{
lean_object* x_389; 
lean_dec(x_367);
lean_dec(x_364);
lean_dec(x_357);
lean_dec(x_346);
if (lean_is_scalar(x_369)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_369;
}
lean_ctor_set(x_389, 0, x_1);
lean_ctor_set(x_389, 1, x_368);
return x_389;
}
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_364);
lean_dec(x_357);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_1);
x_390 = lean_ctor_get(x_366, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_366, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_392 = x_366;
} else {
 lean_dec_ref(x_366);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
}
case 5:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
lean_dec(x_4);
lean_dec(x_3);
x_394 = lean_ctor_get(x_1, 0);
lean_inc(x_394);
x_395 = lean_st_ref_get(x_5, x_6);
lean_dec(x_5);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
x_397 = lean_st_ref_get(x_2, x_396);
lean_dec(x_2);
x_398 = !lean_is_exclusive(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; uint8_t x_403; 
x_399 = lean_ctor_get(x_397, 0);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
x_401 = 0;
lean_inc(x_394);
x_402 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_400, x_394, x_401);
x_403 = lean_name_eq(x_394, x_402);
lean_dec(x_394);
if (x_403 == 0)
{
uint8_t x_404; 
x_404 = !lean_is_exclusive(x_1);
if (x_404 == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_1, 0);
lean_dec(x_405);
lean_ctor_set(x_1, 0, x_402);
lean_ctor_set(x_397, 0, x_1);
return x_397;
}
else
{
lean_object* x_406; 
lean_dec(x_1);
x_406 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_406, 0, x_402);
lean_ctor_set(x_397, 0, x_406);
return x_397;
}
}
else
{
lean_dec(x_402);
lean_ctor_set(x_397, 0, x_1);
return x_397;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; uint8_t x_412; 
x_407 = lean_ctor_get(x_397, 0);
x_408 = lean_ctor_get(x_397, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_397);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = 0;
lean_inc(x_394);
x_411 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_409, x_394, x_410);
x_412 = lean_name_eq(x_394, x_411);
lean_dec(x_394);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_413 = x_1;
} else {
 lean_dec_ref(x_1);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(5, 1, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_408);
return x_415;
}
else
{
lean_object* x_416; 
lean_dec(x_411);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_1);
lean_ctor_set(x_416, 1, x_408);
return x_416;
}
}
}
default: 
{
lean_object* x_417; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_1);
lean_ctor_set(x_417, 1, x_6);
return x_417;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Code_cse_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_normExpr___at_Lean_Compiler_LCNF_Code_cse_go___spec__6(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_normExprs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3;
x_2 = l_Lean_Compiler_LCNF_CSE_State_subst___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Compiler_LCNF_Code_cse___closed__1;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_10);
x_12 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_10, x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_4, x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_10, x_16);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = l_Lean_Compiler_LCNF_Code_cse(x_11, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 4, x_14);
lean_ctor_set(x_12, 0, x_1);
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
lean_ctor_set(x_1, 4, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
x_26 = lean_ctor_get(x_1, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_27 = l_Lean_Compiler_LCNF_Code_cse(x_26, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set(x_31, 4, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cse", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_cse___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_cse___closed__2;
x_2 = l_Lean_Compiler_LCNF_cse___closed__3;
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cse() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_cse___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__2;
x_2 = l_Lean_Compiler_LCNF_cse___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__3;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_CSE_State_map___default___closed__1 = _init_l_Lean_Compiler_LCNF_CSE_State_map___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_State_map___default___closed__1);
l_Lean_Compiler_LCNF_CSE_State_map___default___closed__2 = _init_l_Lean_Compiler_LCNF_CSE_State_map___default___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_State_map___default___closed__2);
l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3 = _init_l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3);
l_Lean_Compiler_LCNF_CSE_State_map___default = _init_l_Lean_Compiler_LCNF_CSE_State_map___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_State_map___default);
l_Lean_Compiler_LCNF_CSE_State_subst___default___closed__1 = _init_l_Lean_Compiler_LCNF_CSE_State_subst___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_State_subst___default___closed__1);
l_Lean_Compiler_LCNF_CSE_State_subst___default = _init_l_Lean_Compiler_LCNF_CSE_State_subst___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_State_subst___default);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse);
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1();
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3);
l_Lean_Compiler_LCNF_Code_cse_go___closed__1 = _init_l_Lean_Compiler_LCNF_Code_cse_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse_go___closed__1);
l_Lean_Compiler_LCNF_Code_cse_go___closed__2 = _init_l_Lean_Compiler_LCNF_Code_cse_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse_go___closed__2);
l_Lean_Compiler_LCNF_Code_cse___closed__1 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__1);
l_Lean_Compiler_LCNF_cse___closed__1 = _init_l_Lean_Compiler_LCNF_cse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__1);
l_Lean_Compiler_LCNF_cse___closed__2 = _init_l_Lean_Compiler_LCNF_cse___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__2);
l_Lean_Compiler_LCNF_cse___closed__3 = _init_l_Lean_Compiler_LCNF_cse___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__3);
l_Lean_Compiler_LCNF_cse___closed__4 = _init_l_Lean_Compiler_LCNF_cse___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__4);
l_Lean_Compiler_LCNF_cse = _init_l_Lean_Compiler_LCNF_cse();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979____closed__3);
res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_979_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
