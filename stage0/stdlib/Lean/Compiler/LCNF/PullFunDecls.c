// Lean compiler output
// Module: Lean.Compiler.LCNF.PullFunDecls
// Imports: Init Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.DependsOn Lean.Compiler.LCNF.PassManager
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
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_pullFunDecls___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_pullFunDecls___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__5;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_pullFunDecls___closed__4;
lean_object* l_Array_qpartition_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_PullFunDecls_pull___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTRAux___at_Lean_Compiler_LCNF_PullFunDecls_attachJps___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTRAux___at_Lean_Compiler_LCNF_PullFunDecls_attachJps___spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_collectUsed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_PullFunDecls_pull___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_sortDeps(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_pullFunDecls;
lean_object* l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__4;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PullFunDecls_attach___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__2(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attach(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PullFunDecls_attach___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__1;
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_pullFunDecls___closed__3;
static lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__1;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__1;
x_3 = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__2;
x_4 = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__3;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__4;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__5;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_7, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Name_quickLt(x_5, x_9);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Lean_Name_quickLt(x_5, x_9);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_10);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = 0;
return x_19;
}
}
}
static lean_object* _init_l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_4);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_15 = lean_nat_add(x_3, x_4);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
lean_inc(x_1);
x_125 = lean_array_get(x_1, x_2, x_17);
lean_inc(x_1);
x_126 = lean_array_get(x_1, x_2, x_3);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec(x_128);
x_130 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_127, x_129);
lean_dec(x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_126, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_131, x_133);
lean_dec(x_131);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = lean_ctor_get_uint8(x_125, sizeof(void*)*2);
lean_dec(x_125);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = lean_ctor_get_uint8(x_126, sizeof(void*)*2);
lean_dec(x_126);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = l_Lean_Name_quickLt(x_129, x_133);
lean_dec(x_133);
lean_dec(x_129);
if (x_137 == 0)
{
x_18 = x_2;
goto block_124;
}
else
{
lean_object* x_138; 
x_138 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_138;
goto block_124;
}
}
else
{
lean_dec(x_133);
lean_dec(x_129);
x_18 = x_2;
goto block_124;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_126, sizeof(void*)*2);
lean_dec(x_126);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_133);
lean_dec(x_129);
x_140 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_140;
goto block_124;
}
else
{
uint8_t x_141; 
x_141 = l_Lean_Name_quickLt(x_129, x_133);
lean_dec(x_133);
lean_dec(x_129);
if (x_141 == 0)
{
x_18 = x_2;
goto block_124;
}
else
{
lean_object* x_142; 
x_142 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_142;
goto block_124;
}
}
}
}
else
{
lean_object* x_143; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_125);
x_143 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_143;
goto block_124;
}
}
else
{
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_125);
x_18 = x_2;
goto block_124;
}
block_124:
{
lean_object* x_19; lean_object* x_61; lean_object* x_62; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_inc(x_1);
x_61 = lean_array_get(x_1, x_18, x_4);
lean_inc(x_1);
x_102 = lean_array_get(x_1, x_18, x_3);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_61, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_103, x_105);
lean_dec(x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_61, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_107, x_109);
lean_dec(x_107);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = lean_ctor_get_uint8(x_61, sizeof(void*)*2);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = lean_ctor_get_uint8(x_102, sizeof(void*)*2);
lean_dec(x_102);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = l_Lean_Name_quickLt(x_105, x_109);
lean_dec(x_109);
lean_dec(x_105);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_box(0);
x_62 = x_114;
goto block_101;
}
else
{
lean_object* x_115; 
lean_dec(x_61);
x_115 = lean_box(0);
x_19 = x_115;
goto block_60;
}
}
else
{
lean_object* x_116; 
lean_dec(x_109);
lean_dec(x_105);
x_116 = lean_box(0);
x_62 = x_116;
goto block_101;
}
}
else
{
uint8_t x_117; 
x_117 = lean_ctor_get_uint8(x_102, sizeof(void*)*2);
lean_dec(x_102);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_109);
lean_dec(x_105);
lean_dec(x_61);
x_118 = lean_box(0);
x_19 = x_118;
goto block_60;
}
else
{
uint8_t x_119; 
x_119 = l_Lean_Name_quickLt(x_105, x_109);
lean_dec(x_109);
lean_dec(x_105);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_box(0);
x_62 = x_120;
goto block_101;
}
else
{
lean_object* x_121; 
lean_dec(x_61);
x_121 = lean_box(0);
x_19 = x_121;
goto block_60;
}
}
}
}
else
{
lean_object* x_122; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_61);
x_122 = lean_box(0);
x_19 = x_122;
goto block_60;
}
}
else
{
lean_object* x_123; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_102);
x_123 = lean_box(0);
x_62 = x_123;
goto block_101;
}
block_60:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_20 = lean_array_swap(x_18, x_3, x_4);
lean_inc(x_1);
x_21 = lean_array_get(x_1, x_20, x_17);
lean_inc(x_1);
x_22 = lean_array_get(x_1, x_20, x_4);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_23, x_25);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_27, x_29);
lean_dec(x_27);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
lean_dec(x_21);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Name_quickLt(x_25, x_29);
lean_dec(x_29);
lean_dec(x_25);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_17);
x_34 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_35 = l_Array_qpartition_loop___rarg(x_1, x_34, x_4, x_22, x_20, x_3, x_3);
x_5 = x_35;
goto block_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_22);
x_36 = lean_array_swap(x_20, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_37 = lean_array_get(x_1, x_36, x_4);
x_38 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_39 = l_Array_qpartition_loop___rarg(x_1, x_38, x_4, x_37, x_36, x_3, x_3);
x_5 = x_39;
goto block_13;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_17);
x_40 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_41 = l_Array_qpartition_loop___rarg(x_1, x_40, x_4, x_22, x_20, x_3, x_3);
x_5 = x_41;
goto block_13;
}
}
else
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_22);
x_43 = lean_array_swap(x_20, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_44 = lean_array_get(x_1, x_43, x_4);
x_45 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_46 = l_Array_qpartition_loop___rarg(x_1, x_45, x_4, x_44, x_43, x_3, x_3);
x_5 = x_46;
goto block_13;
}
else
{
uint8_t x_47; 
x_47 = l_Lean_Name_quickLt(x_25, x_29);
lean_dec(x_29);
lean_dec(x_25);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_17);
x_48 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_49 = l_Array_qpartition_loop___rarg(x_1, x_48, x_4, x_22, x_20, x_3, x_3);
x_5 = x_49;
goto block_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_22);
x_50 = lean_array_swap(x_20, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_51 = lean_array_get(x_1, x_50, x_4);
x_52 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_53 = l_Array_qpartition_loop___rarg(x_1, x_52, x_4, x_51, x_50, x_3, x_3);
x_5 = x_53;
goto block_13;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
x_54 = lean_array_swap(x_20, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_55 = lean_array_get(x_1, x_54, x_4);
x_56 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_57 = l_Array_qpartition_loop___rarg(x_1, x_56, x_4, x_55, x_54, x_3, x_3);
x_5 = x_57;
goto block_13;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_17);
x_58 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_59 = l_Array_qpartition_loop___rarg(x_1, x_58, x_4, x_22, x_20, x_3, x_3);
x_5 = x_59;
goto block_13;
}
}
block_101:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
lean_inc(x_1);
x_63 = lean_array_get(x_1, x_18, x_17);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_64, x_66);
lean_dec(x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_68, x_70);
lean_dec(x_68);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = lean_ctor_get_uint8(x_63, sizeof(void*)*2);
lean_dec(x_63);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = lean_ctor_get_uint8(x_61, sizeof(void*)*2);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Name_quickLt(x_66, x_70);
lean_dec(x_70);
lean_dec(x_66);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_17);
x_75 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_76 = l_Array_qpartition_loop___rarg(x_1, x_75, x_4, x_61, x_18, x_3, x_3);
x_5 = x_76;
goto block_13;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_61);
x_77 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_78 = lean_array_get(x_1, x_77, x_4);
x_79 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_80 = l_Array_qpartition_loop___rarg(x_1, x_79, x_4, x_78, x_77, x_3, x_3);
x_5 = x_80;
goto block_13;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_17);
x_81 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_82 = l_Array_qpartition_loop___rarg(x_1, x_81, x_4, x_61, x_18, x_3, x_3);
x_5 = x_82;
goto block_13;
}
}
else
{
uint8_t x_83; 
x_83 = lean_ctor_get_uint8(x_61, sizeof(void*)*2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_61);
x_84 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_85 = lean_array_get(x_1, x_84, x_4);
x_86 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_87 = l_Array_qpartition_loop___rarg(x_1, x_86, x_4, x_85, x_84, x_3, x_3);
x_5 = x_87;
goto block_13;
}
else
{
uint8_t x_88; 
x_88 = l_Lean_Name_quickLt(x_66, x_70);
lean_dec(x_70);
lean_dec(x_66);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_17);
x_89 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_90 = l_Array_qpartition_loop___rarg(x_1, x_89, x_4, x_61, x_18, x_3, x_3);
x_5 = x_90;
goto block_13;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_61);
x_91 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_92 = lean_array_get(x_1, x_91, x_4);
x_93 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_94 = l_Array_qpartition_loop___rarg(x_1, x_93, x_4, x_92, x_91, x_3, x_3);
x_5 = x_94;
goto block_13;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_61);
x_95 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
lean_inc(x_1);
x_96 = lean_array_get(x_1, x_95, x_4);
x_97 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_98 = l_Array_qpartition_loop___rarg(x_1, x_97, x_4, x_96, x_95, x_3, x_3);
x_5 = x_98;
goto block_13;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_17);
x_99 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1;
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_100 = l_Array_qpartition_loop___rarg(x_1, x_99, x_4, x_61, x_18, x_3, x_3);
x_5 = x_100;
goto block_13;
}
}
}
}
block_13:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_le(x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_9 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1(x_1, x_7, x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_sortDeps(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_List_redLength___rarg(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l_List_toArrayAux___rarg(x_1, x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1(x_8, x_4, x_9, x_7);
lean_dec(x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_9, x_1);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_4);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_15, x_1);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_14;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_4);
x_2 = x_14;
x_4 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
lean_dec(x_8);
x_9 = 1;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps_go(x_1, x_2, x_9, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_set(x_4, x_11, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = 0;
x_14 = l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___spec__1(x_1, x_13, x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_9);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___lambda__1(x_1, x_11, x_16, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = 0;
x_21 = l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___spec__1(x_1, x_20, x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___lambda__1(x_1, x_18, x_24, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Compiler_LCNF_PullFunDecls_findFVarDeps(x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_PullFunDecls_attach(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PullFunDecls_attach___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(x_14, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_PullFunDecls_ToPull_attach(x_12, x_16);
lean_dec(x_12);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_18;
x_9 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attach(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Lean_Compiler_LCNF_PullFunDecls_sortDeps(x_1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PullFunDecls_attach___spec__1(x_8, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PullFunDecls_attach___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_PullFunDecls_attach___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_7, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_9);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_9, x_9);
if (x_13 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_17 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___spec__1(x_7, x_1, x_15, x_16);
if (x_17 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_4);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_array_get_size(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_3);
x_2 = x_21;
x_3 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_22, x_22);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_3);
x_2 = x_21;
x_3 = x_28;
goto _start;
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___spec__1(x_20, x_1, x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_3);
x_2 = x_21;
x_3 = x_33;
goto _start;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_4);
x_2 = x_21;
x_4 = x_35;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Std_RBNode_findCore___at___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___spec__1(x_7, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_9);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__2(x_1, x_2, x_5);
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_dec(x_7);
return x_6;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_7);
if (x_10 == 0)
{
lean_dec(x_7);
return x_6;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__1(x_4, x_1, x_11, x_12);
if (x_13 == 0)
{
return x_6;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps_go(x_1, x_2, x_9, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_set(x_4, x_11, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = 0;
x_14 = l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__2(x_1, x_13, x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_9);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___lambda__1(x_1, x_11, x_16, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = 0;
x_21 = l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__2(x_1, x_20, x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___lambda__1(x_1, x_18, x_24, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Compiler_LCNF_PullFunDecls_findParamsDeps(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_PullFunDecls_attach(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_filterTRAux___at_Lean_Compiler_LCNF_PullFunDecls_attachJps___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_1 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTRAux___at_Lean_Compiler_LCNF_PullFunDecls_attachJps___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_attachJps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_12 = lean_box(0);
x_13 = l_List_filterTRAux___at_Lean_Compiler_LCNF_PullFunDecls_attachJps___spec__1(x_10, x_12);
x_14 = lean_st_ref_get(x_5, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_List_filterTRAux___at_Lean_Compiler_LCNF_PullFunDecls_attachJps___spec__2(x_17, x_12);
x_20 = lean_st_ref_set(x_2, x_19, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_PullFunDecls_attach(x_13, x_1, x_2, x_3, x_4, x_5, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_12, x_2, x_5, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_10, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
lean_inc(x_14);
x_22 = l_Lean_Compiler_LCNF_FunDeclCore_collectUsed(x_14, x_21);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = l_List_appendTR___rarg(x_24, x_4);
x_26 = lean_st_ref_set(x_7, x_25, x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_6, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_take(x_3, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_st_ref_set(x_3, x_17, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_2, 4);
lean_inc(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Compiler_LCNF_PullFunDecls_pull(x_20, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(x_24, x_22, x_3, x_4, x_5, x_6, x_23);
if (x_1 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_PullFunDecls_addToPull___lambda__1(x_2, x_24, x_1, x_11, x_26, x_28, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Compiler_LCNF_PullFunDecls_attachJps(x_30, x_3, x_4, x_5, x_6, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = l_Lean_Compiler_LCNF_PullFunDecls_addToPull___lambda__1(x_2, x_24, x_1, x_11, x_33, x_35, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_PullFunDecls_pull___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_PullFunDecls_pull___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_PullFunDecls_pull___spec__2(x_2, x_8, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Compiler_LCNF_PullFunDecls_pull(x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_LCNF_PullFunDecls_attachParamsDeps(x_7, x_10, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = l_Lean_Compiler_LCNF_PullFunDecls_pull(x_24, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PullFunDecls_pull___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PullFunDecls_pull___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_pull(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_9 = l_Lean_Compiler_LCNF_PullFunDecls_pull(x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_PullFunDecls_attachFVarDeps(x_12, x_10, x_2, x_3, x_4, x_5, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_17 = lean_ptr_addr(x_15);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_dec(x_21);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
size_t x_23; uint8_t x_24; 
x_23 = lean_ptr_addr(x_7);
x_24 = lean_usize_dec_eq(x_23, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 0);
lean_dec(x_27);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_28; 
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_13, 0, x_28);
return x_13;
}
}
else
{
lean_dec(x_15);
lean_dec(x_7);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_32 = lean_ptr_addr(x_29);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_34 = x_1;
} else {
 lean_dec_ref(x_1);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_7);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
size_t x_37; uint8_t x_38; 
x_37 = lean_ptr_addr(x_7);
x_38 = lean_usize_dec_eq(x_37, x_37);
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
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_7);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_30);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 1:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_50 = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(x_49, x_47, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_1 = x_48;
x_6 = x_51;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 2:
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
lean_dec(x_1);
x_59 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_60 = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(x_59, x_57, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_1 = x_58;
x_6 = x_61;
goto _start;
}
else
{
uint8_t x_63; 
lean_dec(x_58);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
case 4:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
x_69 = l_Lean_Compiler_LCNF_PullFunDecls_pull___closed__1;
x_70 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_PullFunDecls_pull___spec__1(x_68, x_69, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; uint8_t x_80; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
x_76 = lean_ctor_get(x_67, 2);
x_77 = lean_ctor_get(x_67, 3);
x_78 = lean_ptr_addr(x_77);
lean_dec(x_77);
x_79 = lean_ptr_addr(x_73);
x_80 = lean_usize_dec_eq(x_78, x_79);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_1);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_1, 0);
lean_dec(x_82);
lean_ctor_set(x_67, 3, x_73);
lean_ctor_set(x_70, 0, x_1);
return x_70;
}
else
{
lean_object* x_83; 
lean_dec(x_1);
lean_ctor_set(x_67, 3, x_73);
x_83 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_83, 0, x_67);
lean_ctor_set(x_70, 0, x_83);
return x_70;
}
}
else
{
lean_free_object(x_67);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_ctor_set(x_70, 0, x_1);
return x_70;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; uint8_t x_91; 
x_84 = lean_ctor_get(x_70, 0);
x_85 = lean_ctor_get(x_67, 0);
x_86 = lean_ctor_get(x_67, 1);
x_87 = lean_ctor_get(x_67, 2);
x_88 = lean_ctor_get(x_67, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_67);
x_89 = lean_ptr_addr(x_88);
lean_dec(x_88);
x_90 = lean_ptr_addr(x_84);
x_91 = lean_usize_dec_eq(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_92 = x_1;
} else {
 lean_dec_ref(x_1);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_87);
lean_ctor_set(x_93, 3, x_84);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(4, 1, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_70, 0, x_94);
return x_70;
}
else
{
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_ctor_set(x_70, 0, x_1);
return x_70;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; size_t x_103; uint8_t x_104; 
x_95 = lean_ctor_get(x_70, 0);
x_96 = lean_ctor_get(x_70, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_70);
x_97 = lean_ctor_get(x_67, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_67, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_67, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_67, 3);
lean_inc(x_100);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 x_101 = x_67;
} else {
 lean_dec_ref(x_67);
 x_101 = lean_box(0);
}
x_102 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_103 = lean_ptr_addr(x_95);
x_104 = lean_usize_dec_eq(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_105 = x_1;
} else {
 lean_dec_ref(x_1);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_106 = lean_alloc_ctor(0, 4, 0);
} else {
 x_106 = x_101;
}
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_98);
lean_ctor_set(x_106, 2, x_99);
lean_ctor_set(x_106, 3, x_95);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(4, 1, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_96);
return x_108;
}
else
{
lean_object* x_109; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_96);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_67);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_70);
if (x_110 == 0)
{
return x_70;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_70, 0);
x_112 = lean_ctor_get(x_70, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_70);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
default: 
{
lean_object* x_114; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_6);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_PullFunDecls_addToPull___lambda__1(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PullFunDecls_addToPull___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_PullFunDecls_addToPull(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_box(0);
x_13 = lean_st_ref_get(x_4, x_5);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_mk_ref(x_12, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
x_18 = l_Lean_Compiler_LCNF_PullFunDecls_pull(x_11, x_16, x_2, x_3, x_4, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_4, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_16, x_22);
lean_dec(x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_4, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_mk_ref(x_12, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_4);
lean_inc(x_29);
x_31 = l_Lean_Compiler_LCNF_PullFunDecls_attach(x_24, x_19, x_29, x_2, x_3, x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_4, x_33);
lean_dec(x_4);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_29, x_35);
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_1, 4, x_32);
lean_ctor_set(x_36, 0, x_1);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_1, 4, x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_18);
if (x_41 == 0)
{
return x_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
x_47 = lean_ctor_get(x_1, 2);
x_48 = lean_ctor_get(x_1, 3);
x_49 = lean_ctor_get(x_1, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_st_ref_get(x_4, x_5);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_mk_ref(x_50, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_54);
x_56 = l_Lean_Compiler_LCNF_PullFunDecls_pull(x_49, x_54, x_2, x_3, x_4, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_4, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_get(x_54, x_60);
lean_dec(x_54);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_get(x_4, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_mk_ref(x_50, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_4);
lean_inc(x_67);
x_69 = l_Lean_Compiler_LCNF_PullFunDecls_attach(x_62, x_57, x_67, x_2, x_3, x_4, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_4, x_71);
lean_dec(x_4);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_get(x_67, x_73);
lean_dec(x_67);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_45);
lean_ctor_set(x_77, 1, x_46);
lean_ctor_set(x_77, 2, x_47);
lean_ctor_set(x_77, 3, x_48);
lean_ctor_set(x_77, 4, x_70);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_56, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_56, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_81 = x_56;
} else {
 lean_dec_ref(x_56);
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
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pullFunDecls", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_pullFunDecls___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_pullFunDecls), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_pullFunDecls___closed__2;
x_2 = l_Lean_Compiler_LCNF_pullFunDecls___closed__3;
x_3 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullFunDecls() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_pullFunDecls___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__2;
x_2 = l_Lean_Compiler_LCNF_pullFunDecls___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__3;
x_3 = 1;
x_4 = l_Lean_registerTraceClass(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DependsOn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__1 = _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__1);
l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__2 = _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__2);
l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__3 = _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__3);
l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__4 = _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__4);
l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__5 = _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull___closed__5);
l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull = _init_l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_instInhabitedToPull);
l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1 = _init_l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1();
lean_mark_persistent(l_Array_qsort_sort___at_Lean_Compiler_LCNF_PullFunDecls_sortDeps___spec__1___closed__1);
l_Lean_Compiler_LCNF_PullFunDecls_pull___closed__1 = _init_l_Lean_Compiler_LCNF_PullFunDecls_pull___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PullFunDecls_pull___closed__1);
l_Lean_Compiler_LCNF_pullFunDecls___closed__1 = _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullFunDecls___closed__1);
l_Lean_Compiler_LCNF_pullFunDecls___closed__2 = _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullFunDecls___closed__2);
l_Lean_Compiler_LCNF_pullFunDecls___closed__3 = _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullFunDecls___closed__3);
l_Lean_Compiler_LCNF_pullFunDecls___closed__4 = _init_l_Lean_Compiler_LCNF_pullFunDecls___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullFunDecls___closed__4);
l_Lean_Compiler_LCNF_pullFunDecls = _init_l_Lean_Compiler_LCNF_pullFunDecls();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullFunDecls);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329____closed__3);
res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_PullFunDecls___hyg_1329_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
