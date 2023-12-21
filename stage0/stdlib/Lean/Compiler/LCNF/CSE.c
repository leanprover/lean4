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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__5;
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__10;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__14;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_State_subst___default;
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2;
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_CSE_State_subst___default___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__16;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_State_map___default___closed__2;
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_cse___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__11;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_Code_cse_go___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_State_map___default___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__18;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__8;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__1;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__7;
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__9;
static lean_object* l_Lean_Compiler_LCNF_Code_cse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse_go___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_CSE_State_subst___default___spec__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Code_cse_go___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__12;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__17;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_State_map___default;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__4;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_toExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_State_map___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_CSE_State_subst___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_State_subst___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_CSE_State_subst___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_CSE_State_subst___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2___rarg), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1;
x_2 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__2___rarg), 8, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_StateRefT_x27_get___at_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_9, 1, x_13);
x_14 = lean_st_ref_set(x_2, x_9, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_apply_1(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_st_ref_set(x_2, x_24, x_10);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstStateM(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_getSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_CSE_getSubst(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2;
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
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2;
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
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_5, x_8, x_9, x_2, x_3);
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
x_18 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_13, x_16, x_17, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_13, x_1, x_2);
lean_ctor_set(x_10, 0, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
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
x_24 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_22, x_1, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_st_ref_set(x_3, x_25, x_11);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_CSE_addEntry___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_addEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CSE_addEntry(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_11);
x_20 = lean_st_ref_set(x_2, x_16, x_17);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_13);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_st_ref_set(x_2, x_26, x_17);
lean_dec(x_2);
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
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_st_ref_take(x_2, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
lean_ctor_set(x_34, 0, x_11);
x_38 = lean_st_ref_set(x_2, x_34, x_35);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_31);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_11);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_st_ref_set(x_2, x_44, x_35);
lean_dec(x_2);
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
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_withNewScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_CSE_withNewScope___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = l_Lean_Compiler_LCNF_eraseLetDecl(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_st_ref_take(x_3, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_fvar___override(x_2);
x_18 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_16, x_11, x_17);
lean_ctor_set(x_13, 1, x_18);
x_19 = lean_st_ref_set(x_3, x_13, x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = l_Lean_Expr_fvar___override(x_2);
x_29 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_27, x_11, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_st_ref_set(x_3, x_30, x_14);
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
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CSE_replaceLet(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = 1;
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_eraseFunDecl(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_st_ref_take(x_3, x_11);
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
x_19 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_17, x_12, x_18);
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
x_30 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_28, x_12, x_29);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CSE_replaceFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_CSE_replaceFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_3, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_1, x_9);
x_15 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_2, x_14, x_4, x_5, x_6, x_7, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__4(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2___boxed), 8, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__3(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_goFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_2, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_12, x_13, x_8);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(x_13, x_15, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
x_20 = lean_st_ref_get(x_2, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Compiler_LCNF_Code_cse_go(x_19, x_2, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_take(x_2, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
lean_ctor_set(x_28, 0, x_23);
x_32 = lean_st_ref_set(x_2, x_28, x_29);
lean_dec(x_2);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_14, x_17, x_25, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_set(x_2, x_36, x_29);
lean_dec(x_2);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_14, x_17, x_25, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_dec(x_24);
x_42 = lean_st_ref_take(x_2, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
lean_ctor_set(x_43, 0, x_23);
x_47 = lean_st_ref_set(x_2, x_43, x_44);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_40);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_st_ref_set(x_2, x_53, x_44);
lean_dec(x_2);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_16);
if (x_58 == 0)
{
return x_16;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_16, 0);
x_60 = lean_ctor_get(x_16, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_16);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_3, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_1, x_9);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
x_16 = lean_st_ref_get(x_3, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_19, x_15, x_1);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(x_2, x_14, x_20, x_4, x_5, x_6, x_7, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2;
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
x_23 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_Code_cse_go___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_12, x_2, x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_16, x_2, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_3, x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_14 = lean_apply_7(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_15);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
x_9 = x_16;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Code_cse_go___spec__7(x_2, x_9, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_2, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(x_14, x_8, x_2, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_Compiler_LCNF_Code_cse_go(x_9, x_2, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(x_1, x_16, x_19);
x_22 = lean_st_ref_take(x_2, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_13);
x_27 = lean_st_ref_set(x_2, x_23, x_24);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_21);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_st_ref_set(x_2, x_33, x_24);
lean_dec(x_2);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_16);
lean_dec(x_1);
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_st_ref_take(x_2, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
lean_ctor_set(x_41, 0, x_13);
x_45 = lean_st_ref_set(x_2, x_41, x_42);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_38);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_st_ref_set(x_2, x_51, x_42);
lean_dec(x_2);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = lean_ctor_get(x_15, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_dec(x_15);
x_58 = lean_st_ref_take(x_2, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
lean_ctor_set(x_59, 0, x_13);
x_63 = lean_st_ref_set(x_2, x_59, x_60);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 0, x_56);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_dec(x_59);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_13);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_st_ref_set(x_2, x_69, x_60);
lean_dec(x_2);
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
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_56);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_st_ref_get(x_2, x_7);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_2);
x_79 = l_Lean_Compiler_LCNF_Code_cse_go(x_74, x_2, x_3, x_4, x_5, x_6, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_80);
x_83 = lean_st_ref_take(x_2, x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
lean_ctor_set(x_84, 0, x_78);
x_88 = lean_st_ref_set(x_2, x_84, x_85);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
lean_ctor_set(x_88, 0, x_82);
return x_88;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
lean_dec(x_84);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_78);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_st_ref_set(x_2, x_94, x_85);
lean_dec(x_2);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_82);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_1);
x_99 = lean_ctor_get(x_79, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 1);
lean_inc(x_100);
lean_dec(x_79);
x_101 = lean_st_ref_take(x_2, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
lean_ctor_set(x_102, 0, x_78);
x_106 = lean_st_ref_set(x_2, x_102, x_103);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_106, 0);
lean_dec(x_108);
lean_ctor_set_tag(x_106, 1);
lean_ctor_set(x_106, 0, x_99);
return x_106;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
lean_dec(x_102);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_78);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_st_ref_set(x_2, x_112, x_103);
lean_dec(x_2);
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
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_114);
return x_116;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Code_cse_go___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = 0;
lean_inc(x_8);
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1(x_10, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 3);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_14);
x_16 = lean_st_ref_get(x_2, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
x_20 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_Code_cse_go___spec__2(x_19, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
x_22 = lean_st_ref_take(x_2, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_26, x_15, x_21);
lean_ctor_set(x_23, 0, x_27);
x_28 = lean_st_ref_set(x_2, x_23, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_9);
x_30 = l_Lean_Compiler_LCNF_Code_cse_go(x_9, x_2, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; size_t x_33; size_t x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_34 = lean_ptr_addr(x_32);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_8);
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
else
{
lean_object* x_39; 
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_41 = lean_ptr_addr(x_12);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_1, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_1, 0);
lean_dec(x_45);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
else
{
lean_object* x_46; 
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_32);
lean_ctor_set(x_30, 0, x_46);
return x_30;
}
}
else
{
lean_dec(x_32);
lean_dec(x_12);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_50 = lean_ptr_addr(x_47);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_52 = x_1;
} else {
 lean_dec_ref(x_1);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_47);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
else
{
size_t x_55; size_t x_56; uint8_t x_57; 
x_55 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_56 = lean_ptr_addr(x_12);
x_57 = lean_usize_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_58 = x_1;
} else {
 lean_dec_ref(x_1);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_47);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_48);
return x_60;
}
else
{
lean_object* x_61; 
lean_dec(x_47);
lean_dec(x_12);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_48);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_30);
if (x_62 == 0)
{
return x_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_30, 0);
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_30);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_23, 0);
x_67 = lean_ctor_get(x_23, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_23);
x_68 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_66, x_15, x_21);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_st_ref_set(x_2, x_69, x_24);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_9);
x_72 = l_Lean_Compiler_LCNF_Code_cse_go(x_9, x_2, x_3, x_4, x_5, x_6, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_77 = lean_ptr_addr(x_73);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_8);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_79 = x_1;
} else {
 lean_dec_ref(x_1);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_12);
lean_ctor_set(x_80, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_74);
return x_81;
}
else
{
size_t x_82; size_t x_83; uint8_t x_84; 
x_82 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_83 = lean_ptr_addr(x_12);
x_84 = lean_usize_dec_eq(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_85 = x_1;
} else {
 lean_dec_ref(x_1);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_12);
lean_ctor_set(x_86, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_75;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_74);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec(x_73);
lean_dec(x_12);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_74);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_89 = lean_ctor_get(x_72, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_72, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_91 = x_72;
} else {
 lean_dec_ref(x_72);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_1);
x_93 = lean_ctor_get(x_20, 0);
lean_inc(x_93);
lean_dec(x_20);
x_94 = l_Lean_Compiler_LCNF_CSE_replaceLet(x_12, x_93, x_2, x_3, x_4, x_5, x_6, x_18);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_1 = x_9;
x_7 = x_95;
goto _start;
}
}
case 1:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_1, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_1, 1);
lean_inc(x_98);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_97);
x_99 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_97, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Compiler_LCNF_Code_cse_go___closed__1;
lean_inc(x_100);
x_103 = l_Lean_Compiler_LCNF_FunDeclCore_toExpr(x_100, x_102);
x_104 = lean_st_ref_get(x_2, x_101);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_103);
x_108 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_Code_cse_go___spec__2(x_107, x_103);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = lean_ctor_get(x_100, 0);
lean_inc(x_109);
x_110 = lean_st_ref_take(x_2, x_106);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_114, x_103, x_109);
lean_ctor_set(x_111, 0, x_115);
x_116 = lean_st_ref_set(x_2, x_111, x_112);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
lean_inc(x_98);
x_118 = l_Lean_Compiler_LCNF_Code_cse_go(x_98, x_2, x_3, x_4, x_5, x_6, x_117);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; size_t x_121; size_t x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ptr_addr(x_98);
lean_dec(x_98);
x_122 = lean_ptr_addr(x_120);
x_123 = lean_usize_dec_eq(x_121, x_122);
if (x_123 == 0)
{
uint8_t x_124; 
lean_dec(x_97);
x_124 = !lean_is_exclusive(x_1);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_1, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_1, 0);
lean_dec(x_126);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_100);
lean_ctor_set(x_118, 0, x_1);
return x_118;
}
else
{
lean_object* x_127; 
lean_dec(x_1);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_100);
lean_ctor_set(x_127, 1, x_120);
lean_ctor_set(x_118, 0, x_127);
return x_118;
}
}
else
{
size_t x_128; size_t x_129; uint8_t x_130; 
x_128 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_129 = lean_ptr_addr(x_100);
x_130 = lean_usize_dec_eq(x_128, x_129);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_1);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_1, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_1, 0);
lean_dec(x_133);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_100);
lean_ctor_set(x_118, 0, x_1);
return x_118;
}
else
{
lean_object* x_134; 
lean_dec(x_1);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_100);
lean_ctor_set(x_134, 1, x_120);
lean_ctor_set(x_118, 0, x_134);
return x_118;
}
}
else
{
lean_dec(x_120);
lean_dec(x_100);
lean_ctor_set(x_118, 0, x_1);
return x_118;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; size_t x_137; size_t x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_118, 0);
x_136 = lean_ctor_get(x_118, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_118);
x_137 = lean_ptr_addr(x_98);
lean_dec(x_98);
x_138 = lean_ptr_addr(x_135);
x_139 = lean_usize_dec_eq(x_137, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_97);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_140 = x_1;
} else {
 lean_dec_ref(x_1);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_100);
lean_ctor_set(x_141, 1, x_135);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_136);
return x_142;
}
else
{
size_t x_143; size_t x_144; uint8_t x_145; 
x_143 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_144 = lean_ptr_addr(x_100);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
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
lean_ctor_set(x_147, 0, x_100);
lean_ctor_set(x_147, 1, x_135);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_136);
return x_148;
}
else
{
lean_object* x_149; 
lean_dec(x_135);
lean_dec(x_100);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_1);
lean_ctor_set(x_149, 1, x_136);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_118);
if (x_150 == 0)
{
return x_118;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_118, 0);
x_152 = lean_ctor_get(x_118, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_118);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_111, 0);
x_155 = lean_ctor_get(x_111, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_111);
x_156 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_CSE_addEntry___spec__1(x_154, x_103, x_109);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_st_ref_set(x_2, x_157, x_112);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
lean_inc(x_98);
x_160 = l_Lean_Compiler_LCNF_Code_cse_go(x_98, x_2, x_3, x_4, x_5, x_6, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; size_t x_164; size_t x_165; uint8_t x_166; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_ptr_addr(x_98);
lean_dec(x_98);
x_165 = lean_ptr_addr(x_161);
x_166 = lean_usize_dec_eq(x_164, x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_97);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_167 = x_1;
} else {
 lean_dec_ref(x_1);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_100);
lean_ctor_set(x_168, 1, x_161);
if (lean_is_scalar(x_163)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_163;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_162);
return x_169;
}
else
{
size_t x_170; size_t x_171; uint8_t x_172; 
x_170 = lean_ptr_addr(x_97);
lean_dec(x_97);
x_171 = lean_ptr_addr(x_100);
x_172 = lean_usize_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
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
lean_ctor_set(x_174, 0, x_100);
lean_ctor_set(x_174, 1, x_161);
if (lean_is_scalar(x_163)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_163;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_162);
return x_175;
}
else
{
lean_object* x_176; 
lean_dec(x_161);
lean_dec(x_100);
if (lean_is_scalar(x_163)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_163;
}
lean_ctor_set(x_176, 0, x_1);
lean_ctor_set(x_176, 1, x_162);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_1);
x_177 = lean_ctor_get(x_160, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_160, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_179 = x_160;
} else {
 lean_dec_ref(x_160);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_103);
lean_dec(x_97);
lean_dec(x_1);
x_181 = lean_ctor_get(x_108, 0);
lean_inc(x_181);
lean_dec(x_108);
x_182 = l_Lean_Compiler_LCNF_CSE_replaceFun(x_100, x_181, x_2, x_3, x_4, x_5, x_6, x_106);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_1 = x_98;
x_7 = x_183;
goto _start;
}
}
else
{
uint8_t x_185; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_99);
if (x_185 == 0)
{
return x_99;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_99, 0);
x_187 = lean_ctor_get(x_99, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_99);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
case 2:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_1, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_1, 1);
lean_inc(x_190);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_189);
x_191 = l_Lean_Compiler_LCNF_Code_cse_goFunDecl(x_189, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_190);
x_194 = l_Lean_Compiler_LCNF_Code_cse_go(x_190, x_2, x_3, x_4, x_5, x_6, x_193);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; size_t x_197; size_t x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_198 = lean_ptr_addr(x_196);
x_199 = lean_usize_dec_eq(x_197, x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_dec(x_189);
x_200 = !lean_is_exclusive(x_1);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_1, 1);
lean_dec(x_201);
x_202 = lean_ctor_get(x_1, 0);
lean_dec(x_202);
lean_ctor_set(x_1, 1, x_196);
lean_ctor_set(x_1, 0, x_192);
lean_ctor_set(x_194, 0, x_1);
return x_194;
}
else
{
lean_object* x_203; 
lean_dec(x_1);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_192);
lean_ctor_set(x_203, 1, x_196);
lean_ctor_set(x_194, 0, x_203);
return x_194;
}
}
else
{
size_t x_204; size_t x_205; uint8_t x_206; 
x_204 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_205 = lean_ptr_addr(x_192);
x_206 = lean_usize_dec_eq(x_204, x_205);
if (x_206 == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_1);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_1, 1);
lean_dec(x_208);
x_209 = lean_ctor_get(x_1, 0);
lean_dec(x_209);
lean_ctor_set(x_1, 1, x_196);
lean_ctor_set(x_1, 0, x_192);
lean_ctor_set(x_194, 0, x_1);
return x_194;
}
else
{
lean_object* x_210; 
lean_dec(x_1);
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_192);
lean_ctor_set(x_210, 1, x_196);
lean_ctor_set(x_194, 0, x_210);
return x_194;
}
}
else
{
lean_dec(x_196);
lean_dec(x_192);
lean_ctor_set(x_194, 0, x_1);
return x_194;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; size_t x_213; size_t x_214; uint8_t x_215; 
x_211 = lean_ctor_get(x_194, 0);
x_212 = lean_ctor_get(x_194, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_194);
x_213 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_214 = lean_ptr_addr(x_211);
x_215 = lean_usize_dec_eq(x_213, x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_189);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_216 = x_1;
} else {
 lean_dec_ref(x_1);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(2, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_192);
lean_ctor_set(x_217, 1, x_211);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_212);
return x_218;
}
else
{
size_t x_219; size_t x_220; uint8_t x_221; 
x_219 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_220 = lean_ptr_addr(x_192);
x_221 = lean_usize_dec_eq(x_219, x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
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
lean_ctor_set(x_223, 0, x_192);
lean_ctor_set(x_223, 1, x_211);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_212);
return x_224;
}
else
{
lean_object* x_225; 
lean_dec(x_211);
lean_dec(x_192);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_1);
lean_ctor_set(x_225, 1, x_212);
return x_225;
}
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_194);
if (x_226 == 0)
{
return x_194;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_194, 0);
x_228 = lean_ctor_get(x_194, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_194);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_191);
if (x_230 == 0)
{
return x_191;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_191, 0);
x_232 = lean_ctor_get(x_191, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_191);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
case 3:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; 
x_234 = lean_ctor_get(x_1, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_1, 1);
lean_inc(x_235);
x_236 = lean_st_ref_get(x_2, x_7);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = 0;
lean_inc(x_234);
x_241 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_239, x_234, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec(x_241);
lean_inc(x_235);
x_243 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5(x_240, x_235, x_2, x_3, x_4, x_5, x_6, x_238);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_name_eq(x_234, x_242);
lean_dec(x_234);
if (x_246 == 0)
{
uint8_t x_247; 
lean_dec(x_235);
x_247 = !lean_is_exclusive(x_1);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_1, 1);
lean_dec(x_248);
x_249 = lean_ctor_get(x_1, 0);
lean_dec(x_249);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_242);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
else
{
lean_object* x_250; 
lean_dec(x_1);
x_250 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_250, 0, x_242);
lean_ctor_set(x_250, 1, x_245);
lean_ctor_set(x_243, 0, x_250);
return x_243;
}
}
else
{
size_t x_251; size_t x_252; uint8_t x_253; 
x_251 = lean_ptr_addr(x_235);
lean_dec(x_235);
x_252 = lean_ptr_addr(x_245);
x_253 = lean_usize_dec_eq(x_251, x_252);
if (x_253 == 0)
{
uint8_t x_254; 
x_254 = !lean_is_exclusive(x_1);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_1, 1);
lean_dec(x_255);
x_256 = lean_ctor_get(x_1, 0);
lean_dec(x_256);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_242);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
else
{
lean_object* x_257; 
lean_dec(x_1);
x_257 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_257, 0, x_242);
lean_ctor_set(x_257, 1, x_245);
lean_ctor_set(x_243, 0, x_257);
return x_243;
}
}
else
{
lean_dec(x_245);
lean_dec(x_242);
lean_ctor_set(x_243, 0, x_1);
return x_243;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_258 = lean_ctor_get(x_243, 0);
x_259 = lean_ctor_get(x_243, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_243);
x_260 = lean_name_eq(x_234, x_242);
lean_dec(x_234);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_235);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_261 = x_1;
} else {
 lean_dec_ref(x_1);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(3, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_242);
lean_ctor_set(x_262, 1, x_258);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_259);
return x_263;
}
else
{
size_t x_264; size_t x_265; uint8_t x_266; 
x_264 = lean_ptr_addr(x_235);
lean_dec(x_235);
x_265 = lean_ptr_addr(x_258);
x_266 = lean_usize_dec_eq(x_264, x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_267 = x_1;
} else {
 lean_dec_ref(x_1);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(3, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_242);
lean_ctor_set(x_268, 1, x_258);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_259);
return x_269;
}
else
{
lean_object* x_270; 
lean_dec(x_258);
lean_dec(x_242);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_1);
lean_ctor_set(x_270, 1, x_259);
return x_270;
}
}
}
}
else
{
lean_object* x_271; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_2);
lean_dec(x_1);
x_271 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_238);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_271;
}
}
case 4:
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_1, 0);
lean_inc(x_272);
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; 
x_274 = lean_ctor_get(x_272, 0);
x_275 = lean_ctor_get(x_272, 1);
x_276 = lean_ctor_get(x_272, 2);
x_277 = lean_ctor_get(x_272, 3);
x_278 = lean_st_ref_get(x_2, x_7);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = 0;
lean_inc(x_276);
x_283 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_281, x_276, x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
lean_dec(x_283);
x_285 = lean_st_ref_get(x_2, x_280);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_275);
x_289 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_288, x_282, x_275);
x_290 = l_Lean_Compiler_LCNF_Code_cse_go___closed__2;
lean_inc(x_277);
x_291 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__6(x_277, x_290, x_2, x_3, x_4, x_5, x_6, x_287);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; size_t x_294; size_t x_295; uint8_t x_296; 
x_293 = lean_ctor_get(x_291, 0);
x_294 = lean_ptr_addr(x_277);
lean_dec(x_277);
x_295 = lean_ptr_addr(x_293);
x_296 = lean_usize_dec_eq(x_294, x_295);
if (x_296 == 0)
{
uint8_t x_297; 
lean_dec(x_276);
lean_dec(x_275);
x_297 = !lean_is_exclusive(x_1);
if (x_297 == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_1, 0);
lean_dec(x_298);
lean_ctor_set(x_272, 3, x_293);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
lean_ctor_set(x_291, 0, x_1);
return x_291;
}
else
{
lean_object* x_299; 
lean_dec(x_1);
lean_ctor_set(x_272, 3, x_293);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
x_299 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_299, 0, x_272);
lean_ctor_set(x_291, 0, x_299);
return x_291;
}
}
else
{
size_t x_300; size_t x_301; uint8_t x_302; 
x_300 = lean_ptr_addr(x_275);
lean_dec(x_275);
x_301 = lean_ptr_addr(x_289);
x_302 = lean_usize_dec_eq(x_300, x_301);
if (x_302 == 0)
{
uint8_t x_303; 
lean_dec(x_276);
x_303 = !lean_is_exclusive(x_1);
if (x_303 == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_1, 0);
lean_dec(x_304);
lean_ctor_set(x_272, 3, x_293);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
lean_ctor_set(x_291, 0, x_1);
return x_291;
}
else
{
lean_object* x_305; 
lean_dec(x_1);
lean_ctor_set(x_272, 3, x_293);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
x_305 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_305, 0, x_272);
lean_ctor_set(x_291, 0, x_305);
return x_291;
}
}
else
{
uint8_t x_306; 
x_306 = lean_name_eq(x_276, x_284);
lean_dec(x_276);
if (x_306 == 0)
{
uint8_t x_307; 
x_307 = !lean_is_exclusive(x_1);
if (x_307 == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_1, 0);
lean_dec(x_308);
lean_ctor_set(x_272, 3, x_293);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
lean_ctor_set(x_291, 0, x_1);
return x_291;
}
else
{
lean_object* x_309; 
lean_dec(x_1);
lean_ctor_set(x_272, 3, x_293);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
x_309 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_309, 0, x_272);
lean_ctor_set(x_291, 0, x_309);
return x_291;
}
}
else
{
lean_dec(x_293);
lean_dec(x_289);
lean_dec(x_284);
lean_free_object(x_272);
lean_dec(x_274);
lean_ctor_set(x_291, 0, x_1);
return x_291;
}
}
}
}
else
{
lean_object* x_310; lean_object* x_311; size_t x_312; size_t x_313; uint8_t x_314; 
x_310 = lean_ctor_get(x_291, 0);
x_311 = lean_ctor_get(x_291, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_291);
x_312 = lean_ptr_addr(x_277);
lean_dec(x_277);
x_313 = lean_ptr_addr(x_310);
x_314 = lean_usize_dec_eq(x_312, x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_276);
lean_dec(x_275);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_315 = x_1;
} else {
 lean_dec_ref(x_1);
 x_315 = lean_box(0);
}
lean_ctor_set(x_272, 3, x_310);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(4, 1, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_272);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_311);
return x_317;
}
else
{
size_t x_318; size_t x_319; uint8_t x_320; 
x_318 = lean_ptr_addr(x_275);
lean_dec(x_275);
x_319 = lean_ptr_addr(x_289);
x_320 = lean_usize_dec_eq(x_318, x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_276);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_321 = x_1;
} else {
 lean_dec_ref(x_1);
 x_321 = lean_box(0);
}
lean_ctor_set(x_272, 3, x_310);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(4, 1, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_272);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_311);
return x_323;
}
else
{
uint8_t x_324; 
x_324 = lean_name_eq(x_276, x_284);
lean_dec(x_276);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_325 = x_1;
} else {
 lean_dec_ref(x_1);
 x_325 = lean_box(0);
}
lean_ctor_set(x_272, 3, x_310);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_289);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(4, 1, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_272);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_311);
return x_327;
}
else
{
lean_object* x_328; 
lean_dec(x_310);
lean_dec(x_289);
lean_dec(x_284);
lean_free_object(x_272);
lean_dec(x_274);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_1);
lean_ctor_set(x_328, 1, x_311);
return x_328;
}
}
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_289);
lean_dec(x_284);
lean_free_object(x_272);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_1);
x_329 = !lean_is_exclusive(x_291);
if (x_329 == 0)
{
return x_291;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_291, 0);
x_331 = lean_ctor_get(x_291, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_291);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
lean_object* x_333; 
lean_free_object(x_272);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_2);
lean_dec(x_1);
x_333 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_280);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; 
x_334 = lean_ctor_get(x_272, 0);
x_335 = lean_ctor_get(x_272, 1);
x_336 = lean_ctor_get(x_272, 2);
x_337 = lean_ctor_get(x_272, 3);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_272);
x_338 = lean_st_ref_get(x_2, x_7);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = 0;
lean_inc(x_336);
x_343 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_341, x_336, x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec(x_343);
x_345 = lean_st_ref_get(x_2, x_340);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
lean_inc(x_335);
x_349 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_348, x_342, x_335);
x_350 = l_Lean_Compiler_LCNF_Code_cse_go___closed__2;
lean_inc(x_337);
x_351 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Code_cse_go___spec__6(x_337, x_350, x_2, x_3, x_4, x_5, x_6, x_347);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; size_t x_355; size_t x_356; uint8_t x_357; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
x_355 = lean_ptr_addr(x_337);
lean_dec(x_337);
x_356 = lean_ptr_addr(x_352);
x_357 = lean_usize_dec_eq(x_355, x_356);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_336);
lean_dec(x_335);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_358 = x_1;
} else {
 lean_dec_ref(x_1);
 x_358 = lean_box(0);
}
x_359 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_359, 0, x_334);
lean_ctor_set(x_359, 1, x_349);
lean_ctor_set(x_359, 2, x_344);
lean_ctor_set(x_359, 3, x_352);
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(4, 1, 0);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_359);
if (lean_is_scalar(x_354)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_354;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_353);
return x_361;
}
else
{
size_t x_362; size_t x_363; uint8_t x_364; 
x_362 = lean_ptr_addr(x_335);
lean_dec(x_335);
x_363 = lean_ptr_addr(x_349);
x_364 = lean_usize_dec_eq(x_362, x_363);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_336);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_365 = x_1;
} else {
 lean_dec_ref(x_1);
 x_365 = lean_box(0);
}
x_366 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_366, 0, x_334);
lean_ctor_set(x_366, 1, x_349);
lean_ctor_set(x_366, 2, x_344);
lean_ctor_set(x_366, 3, x_352);
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(4, 1, 0);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_366);
if (lean_is_scalar(x_354)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_354;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_353);
return x_368;
}
else
{
uint8_t x_369; 
x_369 = lean_name_eq(x_336, x_344);
lean_dec(x_336);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_370 = x_1;
} else {
 lean_dec_ref(x_1);
 x_370 = lean_box(0);
}
x_371 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_371, 0, x_334);
lean_ctor_set(x_371, 1, x_349);
lean_ctor_set(x_371, 2, x_344);
lean_ctor_set(x_371, 3, x_352);
if (lean_is_scalar(x_370)) {
 x_372 = lean_alloc_ctor(4, 1, 0);
} else {
 x_372 = x_370;
}
lean_ctor_set(x_372, 0, x_371);
if (lean_is_scalar(x_354)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_354;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_353);
return x_373;
}
else
{
lean_object* x_374; 
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_344);
lean_dec(x_334);
if (lean_is_scalar(x_354)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_354;
}
lean_ctor_set(x_374, 0, x_1);
lean_ctor_set(x_374, 1, x_353);
return x_374;
}
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_349);
lean_dec(x_344);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_1);
x_375 = lean_ctor_get(x_351, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_351, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_377 = x_351;
} else {
 lean_dec_ref(x_351);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
else
{
lean_object* x_379; 
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_2);
lean_dec(x_1);
x_379 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_340);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_379;
}
}
}
case 5:
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_380 = lean_ctor_get(x_1, 0);
lean_inc(x_380);
x_381 = lean_st_ref_get(x_2, x_7);
lean_dec(x_2);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = lean_ctor_get(x_381, 1);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = 0;
lean_inc(x_380);
x_387 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_385, x_380, x_386);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; uint8_t x_389; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
lean_dec(x_387);
x_389 = lean_name_eq(x_380, x_388);
lean_dec(x_380);
if (x_389 == 0)
{
uint8_t x_390; 
x_390 = !lean_is_exclusive(x_1);
if (x_390 == 0)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_1, 0);
lean_dec(x_391);
lean_ctor_set(x_1, 0, x_388);
lean_ctor_set(x_381, 0, x_1);
return x_381;
}
else
{
lean_object* x_392; 
lean_dec(x_1);
x_392 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_381, 0, x_392);
return x_381;
}
}
else
{
lean_dec(x_388);
lean_ctor_set(x_381, 0, x_1);
return x_381;
}
}
else
{
lean_object* x_393; 
lean_free_object(x_381);
lean_dec(x_380);
lean_dec(x_1);
x_393 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_384);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; 
x_394 = lean_ctor_get(x_381, 0);
x_395 = lean_ctor_get(x_381, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_381);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = 0;
lean_inc(x_380);
x_398 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_396, x_380, x_397);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; uint8_t x_400; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
lean_dec(x_398);
x_400 = lean_name_eq(x_380, x_399);
lean_dec(x_380);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_401 = x_1;
} else {
 lean_dec_ref(x_1);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(5, 1, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_395);
return x_403;
}
else
{
lean_object* x_404; 
lean_dec(x_399);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_1);
lean_ctor_set(x_404, 1, x_395);
return x_404;
}
}
else
{
lean_object* x_405; 
lean_dec(x_380);
lean_dec(x_1);
x_405 = l_Lean_Compiler_LCNF_mkReturnErased(x_3, x_4, x_5, x_6, x_395);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_405;
}
}
}
default: 
{
lean_object* x_406; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_1);
lean_ctor_set(x_406, 1, x_7);
return x_406;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__2(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Code_cse_goFunDecl___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Code_cse_go___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_Code_cse_go___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Code_cse_go___spec__5(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_cse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_CSE_State_map___default___closed__3;
x_2 = l_Lean_Compiler_LCNF_Code_cse___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_cse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Compiler_LCNF_Code_cse___closed__2;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Compiler_LCNF_Code_cse_go(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
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
else
{
uint8_t x_19; 
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_cse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = l_Lean_Compiler_LCNF_Code_cse(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 4, x_16);
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
lean_ctor_set(x_1, 4, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
x_28 = lean_ctor_get(x_1, 4);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_31 = lean_ctor_get(x_1, 5);
lean_inc(x_31);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_32 = l_Lean_Compiler_LCNF_Code_cse(x_28, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_36 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_27);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*6, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*6 + 1, x_30);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Compiler_LCNF_cse___closed__2;
x_4 = l_Lean_Compiler_LCNF_cse___closed__3;
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_LCNF_cse(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__1;
x_2 = l_Lean_Compiler_LCNF_cse___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__4;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__13;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CSE", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__16;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__18;
x_2 = lean_unsigned_to_nat(1057u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__2;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__19;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
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
l_Lean_Compiler_LCNF_CSE_State_subst___default = _init_l_Lean_Compiler_LCNF_CSE_State_subst___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_State_subst___default);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__1);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2 = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse___closed__2);
l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse = _init_l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse();
lean_mark_persistent(l_Lean_Compiler_LCNF_CSE_instMonadFVarSubstMFalse);
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__1();
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_CSE_addEntry___spec__2___closed__3);
l_Lean_Compiler_LCNF_Code_cse_go___closed__1 = _init_l_Lean_Compiler_LCNF_Code_cse_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse_go___closed__1);
l_Lean_Compiler_LCNF_Code_cse_go___closed__2 = _init_l_Lean_Compiler_LCNF_Code_cse_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse_go___closed__2);
l_Lean_Compiler_LCNF_Code_cse___closed__1 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__1);
l_Lean_Compiler_LCNF_Code_cse___closed__2 = _init_l_Lean_Compiler_LCNF_Code_cse___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Code_cse___closed__2);
l_Lean_Compiler_LCNF_cse___closed__1 = _init_l_Lean_Compiler_LCNF_cse___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__1);
l_Lean_Compiler_LCNF_cse___closed__2 = _init_l_Lean_Compiler_LCNF_cse___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__2);
l_Lean_Compiler_LCNF_cse___closed__3 = _init_l_Lean_Compiler_LCNF_cse___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_cse___closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__17);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__18 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__18);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__19 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057____closed__19);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_CSE___hyg_1057_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
