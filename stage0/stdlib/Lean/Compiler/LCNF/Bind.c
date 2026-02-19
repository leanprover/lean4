// Lean compiler output
// Module: Lean.Compiler.LCNF.Bind
// Imports: public import Lean.Compiler.LCNF.InferType
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "`Code.bind` failed, it contains a out of scope join point"};
static const lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`Code.bind` failed, empty `cases` found"};
static const lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2_value;
static lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_CompilerM_codeBind___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM = (const lean_object*)&l_Lean_Compiler_LCNF_instMonadCodeBindCompilerM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isEtaExpandCandidateCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1_value;
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(x_1);
x_6 = lean_apply_3(x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l_Lean_Compiler_LCNF_Code_bind___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_2);
x_7 = lean_apply_3(x_3, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_Code_bind(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_st_ref_get(x_5);
x_10 = lean_st_ref_get(x_3);
x_11 = l_Lean_Compiler_LCNF_getPurity___redArg(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_14);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = lean_unbox(x_13);
lean_dec(x_13);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16, x_18);
lean_dec_ref(x_16);
x_20 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2;
lean_inc_ref(x_7);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_7);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 1, x_1);
lean_ctor_set(x_10, 0, x_21);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_unbox(x_13);
lean_dec(x_13);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_23, x_24);
lean_dec_ref(x_23);
x_26 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2;
lean_inc_ref(x_7);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_7);
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
lean_inc(x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_31);
lean_dec(x_9);
x_32 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_33 = x_10;
} else {
 lean_dec_ref(x_10);
 x_33 = lean_box(0);
}
x_34 = lean_unbox(x_30);
lean_dec(x_30);
x_35 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_32, x_34);
lean_dec_ref(x_32);
x_36 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2;
lean_inc_ref(x_7);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_7);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(3, 2, 0);
} else {
 x_38 = x_33;
 lean_ctor_set_tag(x_38, 3);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_1);
lean_inc(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_3);
return x_17;
}
}
else
{
lean_free_object(x_3);
lean_dec_ref(x_11);
return x_13;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_dec_ref(x_18);
return x_20;
}
}
}
case 1:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
x_28 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set(x_3, 1, x_30);
lean_ctor_set(x_28, 0, x_3);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_3, 1, x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_3);
return x_32;
}
}
else
{
lean_free_object(x_3);
lean_dec_ref(x_26);
return x_28;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_35 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_34, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_36);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_dec_ref(x_33);
return x_35;
}
}
}
case 2:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_3, 0);
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_ctor_get(x_41, 2);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_41, 4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_44);
lean_inc_ref(x_2);
x_45 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_44, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_46);
lean_inc_ref(x_43);
x_47 = l_Lean_Compiler_LCNF_Code_inferParamType(x_1, x_43, x_46, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_41, x_48, x_43, x_46, x_6);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = l_Lean_FVarIdSet_insert(x_4, x_51);
x_53 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_42, x_52, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_3, 1, x_55);
lean_ctor_set(x_3, 0, x_50);
lean_ctor_set(x_53, 0, x_3);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
lean_ctor_set(x_3, 1, x_56);
lean_ctor_set(x_3, 0, x_50);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_3);
return x_57;
}
}
else
{
lean_dec(x_50);
lean_free_object(x_3);
return x_53;
}
}
else
{
uint8_t x_58; 
lean_free_object(x_3);
lean_dec_ref(x_42);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_58 = !lean_is_exclusive(x_49);
if (x_58 == 0)
{
return x_49;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_46);
lean_dec_ref(x_43);
lean_free_object(x_3);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_61 = !lean_is_exclusive(x_47);
if (x_61 == 0)
{
return x_47;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
lean_dec(x_47);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
lean_dec_ref(x_43);
lean_free_object(x_3);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_45;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_3, 0);
x_65 = lean_ctor_get(x_3, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_3);
x_66 = lean_ctor_get(x_64, 2);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_64, 4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_67);
lean_inc_ref(x_2);
x_68 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_67, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_69);
lean_inc_ref(x_66);
x_70 = l_Lean_Compiler_LCNF_Code_inferParamType(x_1, x_66, x_69, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_64, x_71, x_66, x_69, x_6);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = l_Lean_FVarIdSet_insert(x_4, x_74);
x_76 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_65, x_75, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_77);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
else
{
lean_dec(x_73);
return x_76;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_65);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_82 = x_72;
} else {
 lean_dec_ref(x_72);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_69);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_84 = lean_ctor_get(x_70, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_85 = x_70;
} else {
 lean_dec_ref(x_70);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_84);
return x_86;
}
}
else
{
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_68;
}
}
}
case 3:
{
lean_object* x_87; uint8_t x_88; 
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_3, 0);
x_88 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(x_87, x_4);
lean_dec(x_4);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1;
x_90 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(x_89, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
lean_ctor_set(x_90, 0, x_3);
return x_90;
}
else
{
lean_object* x_93; 
lean_dec(x_90);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_3);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec_ref(x_3);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
return x_90;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_3);
return x_97;
}
}
case 4:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; 
x_98 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_98);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_99 = x_3;
} else {
 lean_dec_ref(x_3);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 3);
lean_inc_ref(x_102);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 x_103 = x_98;
} else {
 lean_dec_ref(x_98);
 x_103 = lean_box(0);
}
x_104 = lean_array_size(x_102);
x_105 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_106 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(x_1, x_2, x_104, x_105, x_102, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_126; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_126 = l_Array_isEmpty___redArg(x_107);
if (x_126 == 0)
{
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = lean_box(0);
goto block_125;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3;
x_128 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(x_127, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_128) == 0)
{
lean_dec_ref(x_128);
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = lean_box(0);
goto block_125;
}
else
{
uint8_t x_129; 
lean_dec(x_107);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
return x_128;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
block_125:
{
lean_object* x_113; 
lean_inc(x_107);
x_113 = l_Lean_Compiler_LCNF_mkCasesResultType(x_1, x_107, x_108, x_109, x_110, x_111);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 0);
if (lean_is_scalar(x_103)) {
 x_116 = lean_alloc_ctor(0, 4, 0);
} else {
 x_116 = x_103;
}
lean_ctor_set(x_116, 0, x_100);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_101);
lean_ctor_set(x_116, 3, x_107);
if (lean_is_scalar(x_99)) {
 x_117 = lean_alloc_ctor(4, 1, 0);
} else {
 x_117 = x_99;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_113, 0, x_117);
return x_113;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
lean_dec(x_113);
if (lean_is_scalar(x_103)) {
 x_119 = lean_alloc_ctor(0, 4, 0);
} else {
 x_119 = x_103;
}
lean_ctor_set(x_119, 0, x_100);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_101);
lean_ctor_set(x_119, 3, x_107);
if (lean_is_scalar(x_99)) {
 x_120 = lean_alloc_ctor(4, 1, 0);
} else {
 x_120 = x_99;
}
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_107);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
x_122 = !lean_is_exclusive(x_113);
if (x_122 == 0)
{
return x_113;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_113, 0);
lean_inc(x_123);
lean_dec(x_113);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_132 = !lean_is_exclusive(x_106);
if (x_132 == 0)
{
return x_106;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_106, 0);
lean_inc(x_133);
lean_dec(x_106);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
case 5:
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_4);
x_135 = lean_ctor_get(x_3, 0);
lean_inc(x_135);
lean_dec_ref(x_3);
x_136 = lean_apply_6(x_2, x_135, x_5, x_6, x_7, x_8, lean_box(0));
return x_136;
}
case 6:
{
uint8_t x_137; 
lean_dec(x_4);
x_137 = !lean_is_exclusive(x_3);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_3, 0);
x_139 = 0;
x_140 = l_Lean_Compiler_LCNF_mkAuxParam(x_1, x_138, x_139, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_142);
x_143 = lean_apply_6(x_2, x_142, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
lean_inc(x_6);
lean_inc(x_144);
x_145 = l_Lean_Compiler_LCNF_Code_inferType(x_1, x_144, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_1, x_144, x_6);
lean_dec(x_144);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
lean_dec_ref(x_147);
x_148 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_1, x_141, x_6);
lean_dec(x_6);
lean_dec(x_141);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_148, 0);
lean_dec(x_150);
lean_ctor_set(x_3, 0, x_146);
lean_ctor_set(x_148, 0, x_3);
return x_148;
}
else
{
lean_object* x_151; 
lean_dec(x_148);
lean_ctor_set(x_3, 0, x_146);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_3);
return x_151;
}
}
else
{
uint8_t x_152; 
lean_dec(x_146);
lean_free_object(x_3);
x_152 = !lean_is_exclusive(x_148);
if (x_152 == 0)
{
return x_148;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_148, 0);
lean_inc(x_153);
lean_dec(x_148);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_146);
lean_dec(x_141);
lean_free_object(x_3);
lean_dec(x_6);
x_155 = !lean_is_exclusive(x_147);
if (x_155 == 0)
{
return x_147;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_147, 0);
lean_inc(x_156);
lean_dec(x_147);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_144);
lean_dec(x_141);
lean_free_object(x_3);
lean_dec(x_6);
x_158 = !lean_is_exclusive(x_145);
if (x_158 == 0)
{
return x_145;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_145, 0);
lean_inc(x_159);
lean_dec(x_145);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
else
{
lean_dec(x_141);
lean_free_object(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_143;
}
}
else
{
uint8_t x_161; 
lean_free_object(x_3);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_161 = !lean_is_exclusive(x_140);
if (x_161 == 0)
{
return x_140;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_140, 0);
lean_inc(x_162);
lean_dec(x_140);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_3, 0);
lean_inc(x_164);
lean_dec(x_3);
x_165 = 0;
x_166 = l_Lean_Compiler_LCNF_mkAuxParam(x_1, x_164, x_165, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_168);
x_169 = lean_apply_6(x_2, x_168, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
lean_inc(x_6);
lean_inc(x_170);
x_171 = l_Lean_Compiler_LCNF_Code_inferType(x_1, x_170, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_1, x_170, x_6);
lean_dec(x_170);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
lean_dec_ref(x_173);
x_174 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_1, x_167, x_6);
lean_dec(x_6);
lean_dec(x_167);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_175 = x_174;
} else {
 lean_dec_ref(x_174);
 x_175 = lean_box(0);
}
x_176 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_176, 0, x_172);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_172);
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_179 = x_174;
} else {
 lean_dec_ref(x_174);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_172);
lean_dec(x_167);
lean_dec(x_6);
x_181 = lean_ctor_get(x_173, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_182 = x_173;
} else {
 lean_dec_ref(x_173);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_170);
lean_dec(x_167);
lean_dec(x_6);
x_184 = lean_ctor_get(x_171, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_185 = x_171;
} else {
 lean_dec_ref(x_171);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
return x_186;
}
}
else
{
lean_dec(x_167);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_169;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_187 = lean_ctor_get(x_166, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_188 = x_166;
} else {
 lean_dec_ref(x_166);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
}
case 7:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_3, 0);
x_191 = lean_ctor_get(x_3, 1);
x_192 = lean_ctor_get(x_3, 2);
x_193 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_193);
x_194 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_193, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; size_t x_197; size_t x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = lean_ptr_addr(x_193);
x_198 = lean_ptr_addr(x_196);
x_199 = lean_usize_dec_eq(x_197, x_198);
if (x_199 == 0)
{
uint8_t x_200; 
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
x_200 = !lean_is_exclusive(x_3);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_3, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_3, 2);
lean_dec(x_202);
x_203 = lean_ctor_get(x_3, 1);
lean_dec(x_203);
x_204 = lean_ctor_get(x_3, 0);
lean_dec(x_204);
lean_ctor_set(x_3, 3, x_196);
lean_ctor_set(x_194, 0, x_3);
return x_194;
}
else
{
lean_object* x_205; 
lean_dec(x_3);
x_205 = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(x_205, 0, x_190);
lean_ctor_set(x_205, 1, x_191);
lean_ctor_set(x_205, 2, x_192);
lean_ctor_set(x_205, 3, x_196);
lean_ctor_set(x_194, 0, x_205);
return x_194;
}
}
else
{
lean_dec(x_196);
lean_ctor_set(x_194, 0, x_3);
return x_194;
}
}
else
{
lean_object* x_206; size_t x_207; size_t x_208; uint8_t x_209; 
x_206 = lean_ctor_get(x_194, 0);
lean_inc(x_206);
lean_dec(x_194);
x_207 = lean_ptr_addr(x_193);
x_208 = lean_ptr_addr(x_206);
x_209 = lean_usize_dec_eq(x_207, x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_210 = x_3;
} else {
 lean_dec_ref(x_3);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(7, 4, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_190);
lean_ctor_set(x_211, 1, x_191);
lean_ctor_set(x_211, 2, x_192);
lean_ctor_set(x_211, 3, x_206);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
else
{
lean_object* x_213; 
lean_dec(x_206);
x_213 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_213, 0, x_3);
return x_213;
}
}
}
else
{
lean_dec_ref(x_3);
return x_194;
}
}
case 8:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_3, 0);
x_215 = lean_ctor_get(x_3, 1);
x_216 = lean_ctor_get(x_3, 2);
x_217 = lean_ctor_get(x_3, 3);
x_218 = lean_ctor_get(x_3, 4);
x_219 = lean_ctor_get(x_3, 5);
lean_inc_ref(x_219);
x_220 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_219, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; size_t x_223; size_t x_224; uint8_t x_225; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = lean_ptr_addr(x_219);
x_224 = lean_ptr_addr(x_222);
x_225 = lean_usize_dec_eq(x_223, x_224);
if (x_225 == 0)
{
uint8_t x_226; 
lean_inc_ref(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
x_226 = !lean_is_exclusive(x_3);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_3, 5);
lean_dec(x_227);
x_228 = lean_ctor_get(x_3, 4);
lean_dec(x_228);
x_229 = lean_ctor_get(x_3, 3);
lean_dec(x_229);
x_230 = lean_ctor_get(x_3, 2);
lean_dec(x_230);
x_231 = lean_ctor_get(x_3, 1);
lean_dec(x_231);
x_232 = lean_ctor_get(x_3, 0);
lean_dec(x_232);
lean_ctor_set(x_3, 5, x_222);
lean_ctor_set(x_220, 0, x_3);
return x_220;
}
else
{
lean_object* x_233; 
lean_dec(x_3);
x_233 = lean_alloc_ctor(8, 6, 0);
lean_ctor_set(x_233, 0, x_214);
lean_ctor_set(x_233, 1, x_215);
lean_ctor_set(x_233, 2, x_216);
lean_ctor_set(x_233, 3, x_217);
lean_ctor_set(x_233, 4, x_218);
lean_ctor_set(x_233, 5, x_222);
lean_ctor_set(x_220, 0, x_233);
return x_220;
}
}
else
{
lean_dec(x_222);
lean_ctor_set(x_220, 0, x_3);
return x_220;
}
}
else
{
lean_object* x_234; size_t x_235; size_t x_236; uint8_t x_237; 
x_234 = lean_ctor_get(x_220, 0);
lean_inc(x_234);
lean_dec(x_220);
x_235 = lean_ptr_addr(x_219);
x_236 = lean_ptr_addr(x_234);
x_237 = lean_usize_dec_eq(x_235, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_inc_ref(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_238 = x_3;
} else {
 lean_dec_ref(x_3);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(8, 6, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_214);
lean_ctor_set(x_239, 1, x_215);
lean_ctor_set(x_239, 2, x_216);
lean_ctor_set(x_239, 3, x_217);
lean_ctor_set(x_239, 4, x_218);
lean_ctor_set(x_239, 5, x_234);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_239);
return x_240;
}
else
{
lean_object* x_241; 
lean_dec(x_234);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_3);
return x_241;
}
}
}
else
{
lean_dec_ref(x_3);
return x_220;
}
}
case 9:
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; 
x_242 = lean_ctor_get(x_3, 0);
x_243 = lean_ctor_get(x_3, 1);
x_244 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_245 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_246 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_246);
x_247 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_246, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_247) == 0)
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; size_t x_250; size_t x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_247, 0);
x_250 = lean_ptr_addr(x_246);
x_251 = lean_ptr_addr(x_249);
x_252 = lean_usize_dec_eq(x_250, x_251);
if (x_252 == 0)
{
uint8_t x_253; 
lean_inc(x_243);
lean_inc(x_242);
x_253 = !lean_is_exclusive(x_3);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_3, 2);
lean_dec(x_254);
x_255 = lean_ctor_get(x_3, 1);
lean_dec(x_255);
x_256 = lean_ctor_get(x_3, 0);
lean_dec(x_256);
lean_ctor_set(x_3, 2, x_249);
lean_ctor_set(x_247, 0, x_3);
return x_247;
}
else
{
lean_object* x_257; 
lean_dec(x_3);
x_257 = lean_alloc_ctor(9, 3, 2);
lean_ctor_set(x_257, 0, x_242);
lean_ctor_set(x_257, 1, x_243);
lean_ctor_set(x_257, 2, x_249);
lean_ctor_set_uint8(x_257, sizeof(void*)*3, x_244);
lean_ctor_set_uint8(x_257, sizeof(void*)*3 + 1, x_245);
lean_ctor_set(x_247, 0, x_257);
return x_247;
}
}
else
{
lean_dec(x_249);
lean_ctor_set(x_247, 0, x_3);
return x_247;
}
}
else
{
lean_object* x_258; size_t x_259; size_t x_260; uint8_t x_261; 
x_258 = lean_ctor_get(x_247, 0);
lean_inc(x_258);
lean_dec(x_247);
x_259 = lean_ptr_addr(x_246);
x_260 = lean_ptr_addr(x_258);
x_261 = lean_usize_dec_eq(x_259, x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_inc(x_243);
lean_inc(x_242);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_262 = x_3;
} else {
 lean_dec_ref(x_3);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(9, 3, 2);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_242);
lean_ctor_set(x_263, 1, x_243);
lean_ctor_set(x_263, 2, x_258);
lean_ctor_set_uint8(x_263, sizeof(void*)*3, x_244);
lean_ctor_set_uint8(x_263, sizeof(void*)*3 + 1, x_245);
x_264 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_264, 0, x_263);
return x_264;
}
else
{
lean_object* x_265; 
lean_dec(x_258);
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_3);
return x_265;
}
}
}
else
{
lean_dec_ref(x_3);
return x_247;
}
}
default: 
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_3, 0);
x_267 = lean_ctor_get(x_3, 1);
x_268 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_269 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_270 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_270);
x_271 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_270, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; size_t x_274; size_t x_275; uint8_t x_276; 
x_273 = lean_ctor_get(x_271, 0);
x_274 = lean_ptr_addr(x_270);
x_275 = lean_ptr_addr(x_273);
x_276 = lean_usize_dec_eq(x_274, x_275);
if (x_276 == 0)
{
uint8_t x_277; 
lean_inc(x_267);
lean_inc(x_266);
x_277 = !lean_is_exclusive(x_3);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_3, 2);
lean_dec(x_278);
x_279 = lean_ctor_get(x_3, 1);
lean_dec(x_279);
x_280 = lean_ctor_get(x_3, 0);
lean_dec(x_280);
lean_ctor_set(x_3, 2, x_273);
lean_ctor_set(x_271, 0, x_3);
return x_271;
}
else
{
lean_object* x_281; 
lean_dec(x_3);
x_281 = lean_alloc_ctor(10, 3, 2);
lean_ctor_set(x_281, 0, x_266);
lean_ctor_set(x_281, 1, x_267);
lean_ctor_set(x_281, 2, x_273);
lean_ctor_set_uint8(x_281, sizeof(void*)*3, x_268);
lean_ctor_set_uint8(x_281, sizeof(void*)*3 + 1, x_269);
lean_ctor_set(x_271, 0, x_281);
return x_271;
}
}
else
{
lean_dec(x_273);
lean_ctor_set(x_271, 0, x_3);
return x_271;
}
}
else
{
lean_object* x_282; size_t x_283; size_t x_284; uint8_t x_285; 
x_282 = lean_ctor_get(x_271, 0);
lean_inc(x_282);
lean_dec(x_271);
x_283 = lean_ptr_addr(x_270);
x_284 = lean_ptr_addr(x_282);
x_285 = lean_usize_dec_eq(x_283, x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_inc(x_267);
lean_inc(x_266);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_286 = x_3;
} else {
 lean_dec_ref(x_3);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(10, 3, 2);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_266);
lean_ctor_set(x_287, 1, x_267);
lean_ctor_set(x_287, 2, x_282);
lean_ctor_set_uint8(x_287, sizeof(void*)*3, x_268);
lean_ctor_set_uint8(x_287, sizeof(void*)*3 + 1, x_269);
x_288 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
else
{
lean_object* x_289; 
lean_dec(x_282);
x_289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_289, 0, x_3);
return x_289;
}
}
}
else
{
lean_dec_ref(x_3);
return x_271;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_5, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_5, x_4, x_15);
switch (lean_obj_tag(x_14)) {
case 0:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
x_28 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_27, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_ctor_set(x_14, 2, x_29);
x_17 = x_14;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_30; 
lean_free_object(x_14);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
x_35 = lean_ctor_get(x_14, 2);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
x_36 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_35, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_37);
x_17 = x_38;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
}
}
case 1:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
x_45 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_44, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
lean_ctor_set(x_14, 1, x_46);
x_17 = x_14;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_47; 
lean_free_object(x_14);
lean_dec_ref(x_43);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_14, 0);
x_51 = lean_ctor_get(x_14, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
x_52 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_51, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_17 = x_54;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_50);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
}
default: 
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_14);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_14, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
x_60 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_59, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_ctor_set(x_14, 0, x_61);
x_17 = x_14;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_62; 
lean_free_object(x_14);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_14, 0);
lean_inc(x_65);
lean_dec(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_2);
x_66 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_2, x_65, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_17 = x_68;
x_18 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_70 = x_66;
} else {
 lean_dec_ref(x_66);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
}
block_23:
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_16, x_4, x_17);
x_4 = x_20;
x_5 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(x_12, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(1);
x_10 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(x_1, x_3, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_box(x_2);
x_8 = lean_apply_3(x_1, x_7, x_3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed), 5, 1);
lean_closure_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_box(x_2);
x_8 = lean_apply_3(x_1, x_7, x_3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = lean_expr_instantiate_rev(x_10, x_3);
lean_dec_ref(x_10);
x_13 = 0;
x_14 = l_Lean_Compiler_LCNF_mkAuxParam(x_1, x_12, x_13, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = l_Lean_Expr_fvar___override(x_16);
x_18 = lean_array_push(x_3, x_17);
x_19 = lean_array_push(x_4, x_15);
x_2 = x_11;
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec_ref(x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_expr_instantiate_rev(x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_headBeta(x_24);
x_26 = lean_expr_eqv(x_25, x_24);
lean_dec_ref(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0;
x_2 = x_25;
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_29; 
lean_dec_ref(x_25);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0;
x_9 = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(x_1, x_2, x_8, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Compiler_LCNF_mkNewParams(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Compiler_LCNF_getArrowArity(x_1);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isEtaExpandCandidateCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_3, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
x_10 = ((lean_object*)(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1));
x_11 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2, x_9, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
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
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_etaExpandCore___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_mkFVar(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_size(x_2);
x_10 = 0;
lean_inc_ref(x_2);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(x_9, x_10, x_2);
x_12 = l_Lean_Compiler_LCNF_instantiateForall(x_1, x_11, x_6, x_7);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 0;
x_15 = l_Lean_Compiler_LCNF_mkNewParams(x_14, x_13, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Array_append___redArg(x_2, x_16);
x_18 = lean_array_size(x_16);
x_19 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(x_18, x_10, x_16);
x_20 = lean_box(x_14);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed), 8, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_14, x_3, x_21, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec_ref(x_17);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_12, 0);
lean_inc(x_36);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_etaExpandCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
lean_inc_ref(x_1);
x_9 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_1, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_etaExpandCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_etaExpandCore_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_inc_ref(x_9);
lean_inc_ref(x_7);
lean_inc_ref(x_8);
x_10 = l_Lean_Compiler_LCNF_etaExpandCore_x3f(x_8, x_7, x_9, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_free_object(x_10);
lean_inc_ref(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_16, x_1, x_8, x_14, x_15, x_3);
lean_dec(x_3);
return x_17;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_inc_ref(x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
x_23 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_22, x_1, x_8, x_20, x_21, x_3);
lean_dec(x_3);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_ctor_get(x_8, 2);
x_17 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_16);
x_18 = l_Lean_Compiler_LCNF_etaExpandCore_x3f(x_16, x_17, x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 1)
{
uint8_t x_21; 
lean_inc(x_12);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec_ref(x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_ctor_set(x_8, 3, x_26);
lean_ctor_set(x_7, 0, x_27);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec_ref(x_20);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set(x_8, 3, x_29);
lean_ctor_set(x_7, 0, x_30);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_7);
lean_ctor_set(x_31, 2, x_12);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_11);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
}
else
{
lean_dec(x_20);
lean_free_object(x_8);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_7);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_18, 0);
lean_inc(x_32);
lean_dec(x_18);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_12);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_33 = x_1;
} else {
 lean_dec_ref(x_1);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_ctor_set(x_8, 3, x_35);
lean_ctor_set(x_7, 0, x_36);
if (lean_is_scalar(x_33)) {
 x_37 = lean_alloc_ctor(0, 3, 1);
} else {
 x_37 = x_33;
}
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_7);
lean_ctor_set(x_37, 2, x_12);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_11);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_32);
lean_free_object(x_8);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_7);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_1);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_8);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_7);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
x_48 = lean_ctor_get(x_8, 2);
x_49 = lean_ctor_get(x_8, 3);
x_50 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
lean_inc_ref(x_48);
x_51 = l_Lean_Compiler_LCNF_etaExpandCore_x3f(x_48, x_49, x_45, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_inc(x_44);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_54 = x_1;
} else {
 lean_dec_ref(x_1);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec_ref(x_52);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 2, x_48);
lean_ctor_set(x_58, 3, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_50);
lean_ctor_set(x_7, 0, x_57);
if (lean_is_scalar(x_54)) {
 x_59 = lean_alloc_ctor(0, 3, 1);
} else {
 x_59 = x_54;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
lean_ctor_set(x_59, 2, x_44);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_43);
if (lean_is_scalar(x_53)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_53;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_object* x_61; 
lean_dec(x_52);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_free_object(x_7);
if (lean_is_scalar(x_53)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_53;
}
lean_ctor_set(x_61, 0, x_1);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_free_object(x_7);
lean_dec_ref(x_1);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_63 = x_51;
} else {
 lean_dec_ref(x_51);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_66 = lean_ctor_get(x_1, 2);
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
lean_dec(x_7);
x_68 = lean_ctor_get(x_8, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_71);
x_72 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_73 = x_8;
} else {
 lean_dec_ref(x_8);
 x_73 = lean_box(0);
}
lean_inc_ref(x_70);
x_74 = l_Lean_Compiler_LCNF_etaExpandCore_x3f(x_70, x_71, x_67, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_obj_tag(x_75) == 1)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc(x_66);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_77 = x_1;
} else {
 lean_dec_ref(x_1);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec_ref(x_75);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
if (lean_is_scalar(x_73)) {
 x_81 = lean_alloc_ctor(0, 4, 1);
} else {
 x_81 = x_73;
}
lean_ctor_set(x_81, 0, x_68);
lean_ctor_set(x_81, 1, x_69);
lean_ctor_set(x_81, 2, x_70);
lean_ctor_set(x_81, 3, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_72);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_80);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(0, 3, 1);
} else {
 x_83 = x_77;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_66);
lean_ctor_set_uint8(x_83, sizeof(void*)*3, x_65);
if (lean_is_scalar(x_76)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_76;
}
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_68);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_1);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_73);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_1);
x_86 = lean_ctor_get(x_74, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_87 = x_74;
} else {
 lean_dec_ref(x_74);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_1);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0 = _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0);
l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1 = _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1);
l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2 = _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2);
l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1 = _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1);
l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3 = _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3);
l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0 = _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
