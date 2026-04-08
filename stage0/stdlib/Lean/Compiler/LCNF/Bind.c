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
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getArrowArity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "`Code.bind` failed, it contains a out of scope join point"};
static const lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`Code.bind` failed, empty `cases` found"};
static const lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isEtaExpandCandidateCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg(uint8_t v_pu_1_, lean_object* v_inst_2_, lean_object* v_c_3_, lean_object* v_f_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(v_pu_1_);
v___x_6_ = lean_apply_3(v_inst_2_, v___x_5_, v_c_3_, v_f_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg___boxed(lean_object* v_pu_7_, lean_object* v_inst_8_, lean_object* v_c_9_, lean_object* v_f_10_){
_start:
{
uint8_t v_pu_boxed_11_; lean_object* v_res_12_; 
v_pu_boxed_11_ = lean_unbox(v_pu_7_);
v_res_12_ = l_Lean_Compiler_LCNF_Code_bind___redArg(v_pu_boxed_11_, v_inst_8_, v_c_9_, v_f_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind(lean_object* v_m_13_, uint8_t v_pu_14_, lean_object* v_inst_15_, lean_object* v_c_16_, lean_object* v_f_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_box(v_pu_14_);
v___x_19_ = lean_apply_3(v_inst_15_, v___x_18_, v_c_16_, v_f_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___boxed(lean_object* v_m_20_, lean_object* v_pu_21_, lean_object* v_inst_22_, lean_object* v_c_23_, lean_object* v_f_24_){
_start:
{
uint8_t v_pu_boxed_25_; lean_object* v_res_26_; 
v_pu_boxed_25_ = lean_unbox(v_pu_21_);
v_res_26_ = l_Lean_Compiler_LCNF_Code_bind(v_m_20_, v_pu_boxed_25_, v_inst_22_, v_c_23_, v_f_24_);
return v_res_26_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_27_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
lean_ctor_set(v___x_32_, 2, v___x_31_);
lean_ctor_set(v___x_32_, 3, v___x_31_);
lean_ctor_set(v___x_32_, 4, v___x_30_);
lean_ctor_set(v___x_32_, 5, v___x_30_);
lean_ctor_set(v___x_32_, 6, v___x_30_);
lean_ctor_set(v___x_32_, 7, v___x_30_);
lean_ctor_set(v___x_32_, 8, v___x_30_);
lean_ctor_set(v___x_32_, 9, v___x_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(lean_object* v_msg_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_options_39_; lean_object* v_ref_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_options_39_ = lean_ctor_get(v___y_36_, 2);
v_ref_40_ = lean_ctor_get(v___y_36_, 5);
v___x_41_ = lean_st_ref_get(v___y_37_);
v___x_42_ = lean_st_ref_get(v___y_35_);
v___x_43_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_34_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_66_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_66_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_66_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_66_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_env_48_; lean_object* v_lctx_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_64_; 
v_env_48_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_env_48_);
lean_dec(v___x_41_);
v_lctx_49_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_64_ == 0)
{
lean_object* v_unused_65_; 
v_unused_65_ = lean_ctor_get(v___x_42_, 1);
lean_dec(v_unused_65_);
v___x_51_ = v___x_42_;
v_isShared_52_ = v_isSharedCheck_64_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_lctx_49_);
lean_dec(v___x_42_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_64_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_53_ = lean_unbox(v_a_44_);
lean_dec(v_a_44_);
v___x_54_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_49_, v___x_53_);
lean_dec_ref(v_lctx_49_);
v___x_55_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2);
lean_inc_ref(v_options_39_);
v___x_56_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_56_, 0, v_env_48_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
lean_ctor_set(v___x_56_, 2, v___x_54_);
lean_ctor_set(v___x_56_, 3, v_options_39_);
if (v_isShared_52_ == 0)
{
lean_ctor_set_tag(v___x_51_, 3);
lean_ctor_set(v___x_51_, 1, v_msg_33_);
lean_ctor_set(v___x_51_, 0, v___x_56_);
v___x_58_ = v___x_51_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_msg_33_);
v___x_58_ = v_reuseFailAlloc_63_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; lean_object* v___x_61_; 
lean_inc(v_ref_40_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v_ref_40_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 1);
lean_ctor_set(v___x_46_, 0, v___x_59_);
v___x_61_ = v___x_46_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v___x_42_);
lean_dec(v___x_41_);
lean_dec_ref(v_msg_33_);
v_a_67_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_43_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_43_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___boxed(lean_object* v_msg_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v_msg_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(lean_object* v_00_u03b1_82_, lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v_msg_83_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___boxed(lean_object* v_00_u03b1_91_, lean_object* v_msg_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(v_00_u03b1_91_, v_msg_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
return v_res_99_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(lean_object* v_k_100_, lean_object* v_t_101_){
_start:
{
if (lean_obj_tag(v_t_101_) == 0)
{
lean_object* v_k_102_; lean_object* v_l_103_; lean_object* v_r_104_; uint8_t v___x_105_; 
v_k_102_ = lean_ctor_get(v_t_101_, 1);
v_l_103_ = lean_ctor_get(v_t_101_, 3);
v_r_104_ = lean_ctor_get(v_t_101_, 4);
v___x_105_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_100_, v_k_102_);
switch(v___x_105_)
{
case 0:
{
v_t_101_ = v_l_103_;
goto _start;
}
case 1:
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
default: 
{
v_t_101_ = v_r_104_;
goto _start;
}
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg___boxed(lean_object* v_k_110_, lean_object* v_t_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_k_110_, v_t_111_);
lean_dec(v_t_111_);
lean_dec(v_k_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0));
v___x_116_ = l_Lean_stringToMessageData(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2));
v___x_119_ = l_Lean_stringToMessageData(v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(uint8_t v_pu_120_, lean_object* v_f_121_, lean_object* v_c_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
switch(lean_obj_tag(v_c_122_))
{
case 0:
{
lean_object* v_decl_129_; lean_object* v_k_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_146_; 
v_decl_129_ = lean_ctor_get(v_c_122_, 0);
v_k_130_ = lean_ctor_get(v_c_122_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_146_ == 0)
{
v___x_132_ = v_c_122_;
v_isShared_133_ = v_isSharedCheck_146_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_k_130_);
lean_inc(v_decl_129_);
lean_dec(v_c_122_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_146_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; 
v___x_134_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_130_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_145_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_145_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_145_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_145_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_a_135_);
v___x_140_ = v___x_132_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_decl_129_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_a_135_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_140_);
v___x_142_ = v___x_137_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_del_object(v___x_132_);
lean_dec_ref(v_decl_129_);
return v___x_134_;
}
}
}
case 1:
{
lean_object* v_decl_147_; lean_object* v_k_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_164_; 
v_decl_147_ = lean_ctor_get(v_c_122_, 0);
v_k_148_ = lean_ctor_get(v_c_122_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_164_ == 0)
{
v___x_150_ = v_c_122_;
v_isShared_151_ = v_isSharedCheck_164_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_k_148_);
lean_inc(v_decl_147_);
lean_dec(v_c_122_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_164_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_148_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_163_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_163_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_163_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_163_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_a_153_);
v___x_158_ = v___x_150_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_decl_147_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_a_153_);
v___x_158_ = v_reuseFailAlloc_162_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_160_; 
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_158_);
v___x_160_ = v___x_155_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
else
{
lean_del_object(v___x_150_);
lean_dec_ref(v_decl_147_);
return v___x_152_;
}
}
}
case 2:
{
lean_object* v_decl_165_; lean_object* v_k_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_208_; 
v_decl_165_ = lean_ctor_get(v_c_122_, 0);
v_k_166_ = lean_ctor_get(v_c_122_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_208_ == 0)
{
v___x_168_ = v_c_122_;
v_isShared_169_ = v_isSharedCheck_208_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_k_166_);
lean_inc(v_decl_165_);
lean_dec(v_c_122_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_208_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_params_170_; lean_object* v_value_171_; lean_object* v___x_172_; 
v_params_170_ = lean_ctor_get(v_decl_165_, 2);
lean_inc_ref(v_params_170_);
v_value_171_ = lean_ctor_get(v_decl_165_, 4);
lean_inc_ref(v_value_171_);
lean_inc_ref(v_f_121_);
v___x_172_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_value_171_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_174_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc_n(v_a_173_, 2);
lean_dec_ref(v___x_172_);
lean_inc_ref(v_params_170_);
v___x_174_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_120_, v_params_170_, v_a_173_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref(v___x_174_);
v___x_176_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_120_, v_decl_165_, v_a_175_, v_params_170_, v_a_173_, v_a_125_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_fvarId_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref(v___x_176_);
v_fvarId_178_ = lean_ctor_get(v_a_177_, 0);
lean_inc(v_fvarId_178_);
lean_inc(v_a_123_);
v___x_179_ = l_Lean_FVarIdSet_insert(v_a_123_, v_fvarId_178_);
v___x_180_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_166_, v___x_179_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
lean_dec(v___x_179_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_191_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_191_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_191_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_191_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v_a_181_);
lean_ctor_set(v___x_168_, 0, v_a_177_);
v___x_186_ = v___x_168_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_177_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_a_181_);
v___x_186_ = v_reuseFailAlloc_190_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_188_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_186_);
v___x_188_ = v___x_183_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
else
{
lean_dec(v_a_177_);
lean_del_object(v___x_168_);
return v___x_180_;
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_del_object(v___x_168_);
lean_dec_ref(v_k_166_);
lean_dec_ref(v_f_121_);
v_a_192_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_176_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_176_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_a_173_);
lean_dec_ref(v_params_170_);
lean_del_object(v___x_168_);
lean_dec_ref(v_k_166_);
lean_dec_ref(v_decl_165_);
lean_dec_ref(v_f_121_);
v_a_200_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_174_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_174_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_dec_ref(v_params_170_);
lean_del_object(v___x_168_);
lean_dec_ref(v_k_166_);
lean_dec_ref(v_decl_165_);
lean_dec_ref(v_f_121_);
return v___x_172_;
}
}
}
case 3:
{
lean_object* v_fvarId_209_; uint8_t v___x_210_; 
lean_dec_ref(v_f_121_);
v_fvarId_209_ = lean_ctor_get(v_c_122_, 0);
v___x_210_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_fvarId_209_, v_a_123_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1, &l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1);
v___x_212_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v___x_211_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v___x_212_, 0);
lean_dec(v_unused_220_);
v___x_214_ = v___x_212_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_dec(v___x_212_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v_c_122_);
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_c_122_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_c_122_);
v_a_221_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_212_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_212_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
else
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v_c_122_);
return v___x_229_;
}
}
case 4:
{
lean_object* v_cases_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_295_; 
v_cases_230_ = lean_ctor_get(v_c_122_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_295_ == 0)
{
v___x_232_ = v_c_122_;
v_isShared_233_ = v_isSharedCheck_295_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_cases_230_);
lean_dec(v_c_122_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_295_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_typeName_234_; lean_object* v_discr_235_; lean_object* v_alts_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_293_; 
v_typeName_234_ = lean_ctor_get(v_cases_230_, 0);
v_discr_235_ = lean_ctor_get(v_cases_230_, 2);
v_alts_236_ = lean_ctor_get(v_cases_230_, 3);
v_isSharedCheck_293_ = !lean_is_exclusive(v_cases_230_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_cases_230_, 1);
lean_dec(v_unused_294_);
v___x_238_ = v_cases_230_;
v_isShared_239_ = v_isSharedCheck_293_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_alts_236_);
lean_inc(v_discr_235_);
lean_inc(v_typeName_234_);
lean_dec(v_cases_230_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_293_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
size_t v_sz_240_; size_t v___x_241_; lean_object* v___x_242_; 
v_sz_240_ = lean_array_size(v_alts_236_);
v___x_241_ = ((size_t)0ULL);
v___x_242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(v_pu_120_, v_f_121_, v_sz_240_, v___x_241_, v_alts_236_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref(v___x_242_);
v___x_272_ = lean_array_get_size(v_a_243_);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_nat_dec_eq(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
v___y_245_ = v_a_124_;
v___y_246_ = v_a_125_;
v___y_247_ = v_a_126_;
v___y_248_ = v_a_127_;
goto v___jp_244_;
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3, &l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3);
v___x_276_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v___x_275_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_dec_ref(v___x_276_);
v___y_245_ = v_a_124_;
v___y_246_ = v_a_125_;
v___y_247_ = v_a_126_;
v___y_248_ = v_a_127_;
goto v___jp_244_;
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_a_243_);
lean_del_object(v___x_238_);
lean_dec(v_discr_235_);
lean_dec(v_typeName_234_);
lean_del_object(v___x_232_);
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
v___jp_244_:
{
lean_object* v___x_249_; 
lean_inc(v_a_243_);
v___x_249_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_120_, v_a_243_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_263_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_263_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_263_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_263_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 3, v_a_243_);
lean_ctor_set(v___x_238_, 1, v_a_250_);
v___x_255_ = v___x_238_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_typeName_234_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_a_250_);
lean_ctor_set(v_reuseFailAlloc_262_, 2, v_discr_235_);
lean_ctor_set(v_reuseFailAlloc_262_, 3, v_a_243_);
v___x_255_ = v_reuseFailAlloc_262_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_255_);
v___x_257_ = v___x_232_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_257_);
v___x_259_ = v___x_252_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_a_243_);
lean_del_object(v___x_238_);
lean_dec(v_discr_235_);
lean_dec(v_typeName_234_);
lean_del_object(v___x_232_);
v_a_264_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_249_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_249_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_del_object(v___x_238_);
lean_dec(v_discr_235_);
lean_dec(v_typeName_234_);
lean_del_object(v___x_232_);
v_a_285_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_242_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_242_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_296_; lean_object* v___x_297_; 
v_fvarId_296_ = lean_ctor_get(v_c_122_, 0);
lean_inc(v_fvarId_296_);
lean_dec_ref(v_c_122_);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
v___x_297_ = lean_apply_6(v_f_121_, v_fvarId_296_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
return v___x_297_;
}
case 6:
{
lean_object* v_type_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_355_; 
v_type_298_ = lean_ctor_get(v_c_122_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_355_ == 0)
{
v___x_300_ = v_c_122_;
v_isShared_301_ = v_isSharedCheck_355_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_type_298_);
lean_dec(v_c_122_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_355_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
uint8_t v___x_302_; lean_object* v___x_303_; 
v___x_302_ = 0;
v___x_303_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_120_, v_type_298_, v___x_302_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v_fvarId_305_; lean_object* v___x_306_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref(v___x_303_);
v_fvarId_305_ = lean_ctor_get(v_a_304_, 0);
lean_inc(v_a_127_);
lean_inc_ref(v_a_126_);
lean_inc(v_a_125_);
lean_inc_ref(v_a_124_);
lean_inc(v_fvarId_305_);
v___x_306_ = lean_apply_6(v_f_121_, v_fvarId_305_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, lean_box(0));
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_n(v_a_307_, 2);
lean_dec_ref(v___x_306_);
v___x_308_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_120_, v_a_307_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_308_);
v___x_310_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_120_, v_a_307_, v_a_125_);
lean_dec(v_a_307_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_311_; 
lean_dec_ref(v___x_310_);
v___x_311_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_120_, v_a_304_, v_a_125_);
lean_dec(v_a_304_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_321_; 
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v___x_311_, 0);
lean_dec(v_unused_322_);
v___x_313_ = v___x_311_;
v_isShared_314_ = v_isSharedCheck_321_;
goto v_resetjp_312_;
}
else
{
lean_dec(v___x_311_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_321_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v_a_309_);
v___x_316_ = v___x_300_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_309_);
v___x_316_ = v_reuseFailAlloc_320_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_318_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_316_);
v___x_318_ = v___x_313_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_dec(v_a_309_);
lean_del_object(v___x_300_);
v_a_323_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_311_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_311_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_a_309_);
lean_dec(v_a_304_);
lean_del_object(v___x_300_);
v_a_331_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_310_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_310_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_a_307_);
lean_dec(v_a_304_);
lean_del_object(v___x_300_);
v_a_339_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_308_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_308_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_dec(v_a_304_);
lean_del_object(v___x_300_);
return v___x_306_;
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_del_object(v___x_300_);
lean_dec_ref(v_f_121_);
v_a_347_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_303_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_303_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_356_; lean_object* v_i_357_; lean_object* v_y_358_; lean_object* v_k_359_; lean_object* v___x_360_; 
v_fvarId_356_ = lean_ctor_get(v_c_122_, 0);
v_i_357_ = lean_ctor_get(v_c_122_, 1);
v_y_358_ = lean_ctor_get(v_c_122_, 2);
v_k_359_ = lean_ctor_get(v_c_122_, 3);
lean_inc_ref(v_k_359_);
v___x_360_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_359_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_385_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_385_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_385_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_385_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
size_t v___x_365_; size_t v___x_366_; uint8_t v___x_367_; 
v___x_365_ = lean_ptr_addr(v_k_359_);
v___x_366_ = lean_ptr_addr(v_a_361_);
v___x_367_ = lean_usize_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
lean_inc(v_y_358_);
lean_inc(v_i_357_);
lean_inc(v_fvarId_356_);
v_isSharedCheck_377_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; lean_object* v_unused_380_; lean_object* v_unused_381_; 
v_unused_378_ = lean_ctor_get(v_c_122_, 3);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_c_122_, 2);
lean_dec(v_unused_379_);
v_unused_380_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_380_);
v_unused_381_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_381_);
v___x_369_ = v_c_122_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_c_122_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 3, v_a_361_);
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_fvarId_356_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_i_357_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_y_358_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_a_361_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_372_);
v___x_374_ = v___x_363_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v___x_383_; 
lean_dec(v_a_361_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v_c_122_);
v___x_383_ = v___x_363_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_c_122_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_dec_ref(v_c_122_);
return v___x_360_;
}
}
case 8:
{
lean_object* v_fvarId_386_; lean_object* v_i_387_; lean_object* v_y_388_; lean_object* v_k_389_; lean_object* v___x_390_; 
v_fvarId_386_ = lean_ctor_get(v_c_122_, 0);
v_i_387_ = lean_ctor_get(v_c_122_, 1);
v_y_388_ = lean_ctor_get(v_c_122_, 2);
v_k_389_ = lean_ctor_get(v_c_122_, 3);
lean_inc_ref(v_k_389_);
v___x_390_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_389_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_415_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_415_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_415_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_415_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
size_t v___x_395_; size_t v___x_396_; uint8_t v___x_397_; 
v___x_395_ = lean_ptr_addr(v_k_389_);
v___x_396_ = lean_ptr_addr(v_a_391_);
v___x_397_ = lean_usize_dec_eq(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_407_; 
lean_inc(v_y_388_);
lean_inc(v_i_387_);
lean_inc(v_fvarId_386_);
v_isSharedCheck_407_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; lean_object* v_unused_409_; lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_408_ = lean_ctor_get(v_c_122_, 3);
lean_dec(v_unused_408_);
v_unused_409_ = lean_ctor_get(v_c_122_, 2);
lean_dec(v_unused_409_);
v_unused_410_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_411_);
v___x_399_ = v_c_122_;
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_c_122_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_407_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 3, v_a_391_);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_fvarId_386_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_i_387_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_y_388_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_a_391_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_404_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_402_);
v___x_404_ = v___x_393_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v___x_413_; 
lean_dec(v_a_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v_c_122_);
v___x_413_ = v___x_393_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_c_122_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_dec_ref(v_c_122_);
return v___x_390_;
}
}
case 9:
{
lean_object* v_fvarId_416_; lean_object* v_i_417_; lean_object* v_offset_418_; lean_object* v_y_419_; lean_object* v_ty_420_; lean_object* v_k_421_; lean_object* v___x_422_; 
v_fvarId_416_ = lean_ctor_get(v_c_122_, 0);
v_i_417_ = lean_ctor_get(v_c_122_, 1);
v_offset_418_ = lean_ctor_get(v_c_122_, 2);
v_y_419_ = lean_ctor_get(v_c_122_, 3);
v_ty_420_ = lean_ctor_get(v_c_122_, 4);
v_k_421_ = lean_ctor_get(v_c_122_, 5);
lean_inc_ref(v_k_421_);
v___x_422_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_421_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_449_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_449_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_449_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_449_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
size_t v___x_427_; size_t v___x_428_; uint8_t v___x_429_; 
v___x_427_ = lean_ptr_addr(v_k_421_);
v___x_428_ = lean_ptr_addr(v_a_423_);
v___x_429_ = lean_usize_dec_eq(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_439_; 
lean_inc_ref(v_ty_420_);
lean_inc(v_y_419_);
lean_inc(v_offset_418_);
lean_inc(v_i_417_);
lean_inc(v_fvarId_416_);
v_isSharedCheck_439_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_439_ == 0)
{
lean_object* v_unused_440_; lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; 
v_unused_440_ = lean_ctor_get(v_c_122_, 5);
lean_dec(v_unused_440_);
v_unused_441_ = lean_ctor_get(v_c_122_, 4);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_c_122_, 3);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_c_122_, 2);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_445_);
v___x_431_ = v_c_122_;
v_isShared_432_ = v_isSharedCheck_439_;
goto v_resetjp_430_;
}
else
{
lean_dec(v_c_122_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_439_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 5, v_a_423_);
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_fvarId_416_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_i_417_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_offset_418_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_y_419_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_ty_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v_a_423_);
v___x_434_ = v_reuseFailAlloc_438_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_434_);
v___x_436_ = v___x_425_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_object* v___x_447_; 
lean_dec(v_a_423_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v_c_122_);
v___x_447_ = v___x_425_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_c_122_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_dec_ref(v_c_122_);
return v___x_422_;
}
}
case 10:
{
lean_object* v_fvarId_450_; lean_object* v_cidx_451_; lean_object* v_k_452_; lean_object* v___x_453_; 
v_fvarId_450_ = lean_ctor_get(v_c_122_, 0);
v_cidx_451_ = lean_ctor_get(v_c_122_, 1);
v_k_452_ = lean_ctor_get(v_c_122_, 2);
lean_inc_ref(v_k_452_);
v___x_453_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_452_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_477_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_477_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_477_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_477_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
size_t v___x_458_; size_t v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_ptr_addr(v_k_452_);
v___x_459_ = lean_ptr_addr(v_a_454_);
v___x_460_ = lean_usize_dec_eq(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_470_; 
lean_inc(v_cidx_451_);
lean_inc(v_fvarId_450_);
v_isSharedCheck_470_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; lean_object* v_unused_472_; lean_object* v_unused_473_; 
v_unused_471_ = lean_ctor_get(v_c_122_, 2);
lean_dec(v_unused_471_);
v_unused_472_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_472_);
v_unused_473_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_473_);
v___x_462_ = v_c_122_;
v_isShared_463_ = v_isSharedCheck_470_;
goto v_resetjp_461_;
}
else
{
lean_dec(v_c_122_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_470_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 2, v_a_454_);
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_fvarId_450_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_cidx_451_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_a_454_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_465_);
v___x_467_ = v___x_456_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
else
{
lean_object* v___x_475_; 
lean_dec(v_a_454_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_c_122_);
v___x_475_ = v___x_456_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_c_122_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
else
{
lean_dec_ref(v_c_122_);
return v___x_453_;
}
}
case 11:
{
lean_object* v_fvarId_478_; lean_object* v_n_479_; uint8_t v_check_480_; uint8_t v_persistent_481_; lean_object* v_k_482_; lean_object* v___x_483_; 
v_fvarId_478_ = lean_ctor_get(v_c_122_, 0);
v_n_479_ = lean_ctor_get(v_c_122_, 1);
v_check_480_ = lean_ctor_get_uint8(v_c_122_, sizeof(void*)*3);
v_persistent_481_ = lean_ctor_get_uint8(v_c_122_, sizeof(void*)*3 + 1);
v_k_482_ = lean_ctor_get(v_c_122_, 2);
lean_inc_ref(v_k_482_);
v___x_483_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_482_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_507_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_507_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_507_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_507_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
size_t v___x_488_; size_t v___x_489_; uint8_t v___x_490_; 
v___x_488_ = lean_ptr_addr(v_k_482_);
v___x_489_ = lean_ptr_addr(v_a_484_);
v___x_490_ = lean_usize_dec_eq(v___x_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_500_; 
lean_inc(v_n_479_);
lean_inc(v_fvarId_478_);
v_isSharedCheck_500_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; lean_object* v_unused_502_; lean_object* v_unused_503_; 
v_unused_501_ = lean_ctor_get(v_c_122_, 2);
lean_dec(v_unused_501_);
v_unused_502_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_502_);
v_unused_503_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_503_);
v___x_492_ = v_c_122_;
v_isShared_493_ = v_isSharedCheck_500_;
goto v_resetjp_491_;
}
else
{
lean_dec(v_c_122_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_500_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 2, v_a_484_);
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fvarId_478_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_n_479_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_a_484_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*3, v_check_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*3 + 1, v_persistent_481_);
v___x_495_ = v_reuseFailAlloc_499_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_497_; 
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_495_);
v___x_497_ = v___x_486_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v___x_505_; 
lean_dec(v_a_484_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v_c_122_);
v___x_505_ = v___x_486_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_c_122_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_dec_ref(v_c_122_);
return v___x_483_;
}
}
case 12:
{
lean_object* v_fvarId_508_; lean_object* v_n_509_; uint8_t v_check_510_; uint8_t v_persistent_511_; lean_object* v_k_512_; lean_object* v___x_513_; 
v_fvarId_508_ = lean_ctor_get(v_c_122_, 0);
v_n_509_ = lean_ctor_get(v_c_122_, 1);
v_check_510_ = lean_ctor_get_uint8(v_c_122_, sizeof(void*)*3);
v_persistent_511_ = lean_ctor_get_uint8(v_c_122_, sizeof(void*)*3 + 1);
v_k_512_ = lean_ctor_get(v_c_122_, 2);
lean_inc_ref(v_k_512_);
v___x_513_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_512_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_537_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_537_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_537_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_537_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
size_t v___x_518_; size_t v___x_519_; uint8_t v___x_520_; 
v___x_518_ = lean_ptr_addr(v_k_512_);
v___x_519_ = lean_ptr_addr(v_a_514_);
v___x_520_ = lean_usize_dec_eq(v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_530_; 
lean_inc(v_n_509_);
lean_inc(v_fvarId_508_);
v_isSharedCheck_530_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; lean_object* v_unused_532_; lean_object* v_unused_533_; 
v_unused_531_ = lean_ctor_get(v_c_122_, 2);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_533_);
v___x_522_ = v_c_122_;
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
else
{
lean_dec(v_c_122_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 2, v_a_514_);
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(12, 3, 2);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_fvarId_508_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_n_509_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_a_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3, v_check_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3 + 1, v_persistent_511_);
v___x_525_ = v_reuseFailAlloc_529_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_525_);
v___x_527_ = v___x_516_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_535_; 
lean_dec(v_a_514_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v_c_122_);
v___x_535_ = v___x_516_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_c_122_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
else
{
lean_dec_ref(v_c_122_);
return v___x_513_;
}
}
default: 
{
lean_object* v_fvarId_538_; lean_object* v_k_539_; lean_object* v___x_540_; 
v_fvarId_538_ = lean_ctor_get(v_c_122_, 0);
v_k_539_ = lean_ctor_get(v_c_122_, 1);
lean_inc_ref(v_k_539_);
v___x_540_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_539_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_563_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_563_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_563_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_563_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
size_t v___x_545_; size_t v___x_546_; uint8_t v___x_547_; 
v___x_545_ = lean_ptr_addr(v_k_539_);
v___x_546_ = lean_ptr_addr(v_a_541_);
v___x_547_ = lean_usize_dec_eq(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_557_; 
lean_inc(v_fvarId_538_);
v_isSharedCheck_557_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_558_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_559_);
v___x_549_ = v_c_122_;
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
else
{
lean_dec(v_c_122_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v_a_541_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_fvarId_538_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_a_541_);
v___x_552_ = v_reuseFailAlloc_556_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_554_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_552_);
v___x_554_ = v___x_543_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v___x_561_; 
lean_dec(v_a_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v_c_122_);
v___x_561_ = v___x_543_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_c_122_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_dec_ref(v_c_122_);
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(uint8_t v_pu_564_, lean_object* v_f_565_, size_t v_sz_566_, size_t v_i_567_, lean_object* v_bs_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v___x_575_; 
v___x_575_ = lean_usize_dec_lt(v_i_567_, v_sz_566_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec_ref(v_f_565_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_bs_568_);
return v___x_576_;
}
else
{
lean_object* v_v_577_; lean_object* v___x_578_; lean_object* v_bs_x27_579_; lean_object* v_a_581_; 
v_v_577_ = lean_array_uget(v_bs_568_, v_i_567_);
v___x_578_ = lean_unsigned_to_nat(0u);
v_bs_x27_579_ = lean_array_uset(v_bs_568_, v_i_567_, v___x_578_);
switch(lean_obj_tag(v_v_577_))
{
case 0:
{
lean_object* v_ctorName_586_; lean_object* v_params_587_; lean_object* v_code_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_605_; 
v_ctorName_586_ = lean_ctor_get(v_v_577_, 0);
v_params_587_ = lean_ctor_get(v_v_577_, 1);
v_code_588_ = lean_ctor_get(v_v_577_, 2);
v_isSharedCheck_605_ = !lean_is_exclusive(v_v_577_);
if (v_isSharedCheck_605_ == 0)
{
v___x_590_ = v_v_577_;
v_isShared_591_ = v_isSharedCheck_605_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_code_588_);
lean_inc(v_params_587_);
lean_inc(v_ctorName_586_);
lean_dec(v_v_577_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_605_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; 
lean_inc_ref(v_f_565_);
v___x_592_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_564_, v_f_565_, v_code_588_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 2, v_a_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_ctorName_586_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_params_587_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_a_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v_a_581_ = v___x_595_;
goto v___jp_580_;
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_del_object(v___x_590_);
lean_dec_ref(v_params_587_);
lean_dec(v_ctorName_586_);
lean_dec_ref(v_bs_x27_579_);
lean_dec_ref(v_f_565_);
v_a_597_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_592_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_592_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
case 1:
{
lean_object* v_info_606_; lean_object* v_code_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_624_; 
v_info_606_ = lean_ctor_get(v_v_577_, 0);
v_code_607_ = lean_ctor_get(v_v_577_, 1);
v_isSharedCheck_624_ = !lean_is_exclusive(v_v_577_);
if (v_isSharedCheck_624_ == 0)
{
v___x_609_ = v_v_577_;
v_isShared_610_ = v_isSharedCheck_624_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_code_607_);
lean_inc(v_info_606_);
lean_dec(v_v_577_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_624_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; 
lean_inc_ref(v_f_565_);
v___x_611_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_564_, v_f_565_, v_code_607_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref(v___x_611_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_a_612_);
v___x_614_ = v___x_609_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_info_606_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_a_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
v_a_581_ = v___x_614_;
goto v___jp_580_;
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_del_object(v___x_609_);
lean_dec_ref(v_info_606_);
lean_dec_ref(v_bs_x27_579_);
lean_dec_ref(v_f_565_);
v_a_616_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_611_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_611_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
default: 
{
lean_object* v_code_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_642_; 
v_code_625_ = lean_ctor_get(v_v_577_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_v_577_);
if (v_isSharedCheck_642_ == 0)
{
v___x_627_ = v_v_577_;
v_isShared_628_ = v_isSharedCheck_642_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_code_625_);
lean_dec(v_v_577_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_642_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; 
lean_inc_ref(v_f_565_);
v___x_629_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_564_, v_f_565_, v_code_625_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref(v___x_629_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v_a_630_);
v___x_632_ = v___x_627_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
v_a_581_ = v___x_632_;
goto v___jp_580_;
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_del_object(v___x_627_);
lean_dec_ref(v_bs_x27_579_);
lean_dec_ref(v_f_565_);
v_a_634_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_629_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_629_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
v___jp_580_:
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_567_, v___x_582_);
v___x_584_ = lean_array_uset(v_bs_x27_579_, v_i_567_, v_a_581_);
v_i_567_ = v___x_583_;
v_bs_568_ = v___x_584_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2___boxed(lean_object* v_pu_643_, lean_object* v_f_644_, lean_object* v_sz_645_, lean_object* v_i_646_, lean_object* v_bs_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
uint8_t v_pu_boxed_654_; size_t v_sz_boxed_655_; size_t v_i_boxed_656_; lean_object* v_res_657_; 
v_pu_boxed_654_ = lean_unbox(v_pu_643_);
v_sz_boxed_655_ = lean_unbox_usize(v_sz_645_);
lean_dec(v_sz_645_);
v_i_boxed_656_ = lean_unbox_usize(v_i_646_);
lean_dec(v_i_646_);
v_res_657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(v_pu_boxed_654_, v_f_644_, v_sz_boxed_655_, v_i_boxed_656_, v_bs_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___boxed(lean_object* v_pu_658_, lean_object* v_f_659_, lean_object* v_c_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
uint8_t v_pu_boxed_667_; lean_object* v_res_668_; 
v_pu_boxed_667_ = lean_unbox(v_pu_658_);
v_res_668_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_boxed_667_, v_f_659_, v_c_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(lean_object* v_00_u03b2_669_, lean_object* v_k_670_, lean_object* v_t_671_){
_start:
{
uint8_t v___x_672_; 
v___x_672_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_k_670_, v_t_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___boxed(lean_object* v_00_u03b2_673_, lean_object* v_k_674_, lean_object* v_t_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(v_00_u03b2_673_, v_k_674_, v_t_675_);
lean_dec(v_t_675_);
lean_dec(v_k_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(uint8_t v_pu_678_, lean_object* v_c_679_, lean_object* v_f_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_box(1);
v___x_687_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_678_, v_f_680_, v_c_679_, v___x_686_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind___boxed(lean_object* v_pu_688_, lean_object* v_c_689_, lean_object* v_f_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
uint8_t v_pu_boxed_696_; lean_object* v_res_697_; 
v_pu_boxed_696_ = lean_unbox(v_pu_688_);
v_res_697_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v_pu_boxed_696_, v_c_689_, v_f_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0(lean_object* v_f_700_, lean_object* v_ctx_701_, lean_object* v_fvarId_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_apply_2(v_f_700_, v_fvarId_702_, v_ctx_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(lean_object* v_inst_704_, uint8_t v_pu_705_, lean_object* v_c_706_, lean_object* v_f_707_, lean_object* v_ctx_708_){
_start:
{
lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___f_709_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_709_, 0, v_f_707_);
lean_closure_set(v___f_709_, 1, v_ctx_708_);
v___x_710_ = lean_box(v_pu_705_);
v___x_711_ = lean_apply_3(v_inst_704_, v___x_710_, v_c_706_, v___f_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed(lean_object* v_inst_712_, lean_object* v_pu_713_, lean_object* v_c_714_, lean_object* v_f_715_, lean_object* v_ctx_716_){
_start:
{
uint8_t v_pu_21__boxed_717_; lean_object* v_res_718_; 
v_pu_21__boxed_717_ = lean_unbox(v_pu_713_);
v_res_718_ = l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(v_inst_712_, v_pu_21__boxed_717_, v_c_714_, v_f_715_, v_ctx_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg(lean_object* v_inst_719_){
_start:
{
lean_object* v___f_720_; 
v___f_720_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_720_, 0, v_inst_719_);
return v___f_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT(lean_object* v_m_721_, lean_object* v_00_u03c1_722_, lean_object* v_inst_723_){
_start:
{
lean_object* v___f_724_; 
v___f_724_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_724_, 0, v_inst_723_);
return v___f_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0(lean_object* v_f_725_, lean_object* v_sref_726_, lean_object* v_fvarId_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_apply_2(v_f_725_, v_fvarId_727_, v_sref_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(lean_object* v_inst_729_, uint8_t v_pu_730_, lean_object* v_c_731_, lean_object* v_f_732_, lean_object* v_sref_733_){
_start:
{
lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___f_734_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0), 3, 2);
lean_closure_set(v___f_734_, 0, v_f_732_);
lean_closure_set(v___f_734_, 1, v_sref_733_);
v___x_735_ = lean_box(v_pu_730_);
v___x_736_ = lean_apply_3(v_inst_729_, v___x_735_, v_c_731_, v___f_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed(lean_object* v_inst_737_, lean_object* v_pu_738_, lean_object* v_c_739_, lean_object* v_f_740_, lean_object* v_sref_741_){
_start:
{
uint8_t v_pu_23__boxed_742_; lean_object* v_res_743_; 
v_pu_23__boxed_742_ = lean_unbox(v_pu_738_);
v_res_743_ = l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(v_inst_737_, v_pu_23__boxed_742_, v_c_739_, v_f_740_, v_sref_741_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg(lean_object* v_inst_744_){
_start:
{
lean_object* v___f_745_; 
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_745_, 0, v_inst_744_);
return v___f_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld(lean_object* v_00_u03c9_746_, lean_object* v_m_747_, lean_object* v_00_u03c3_748_, lean_object* v_inst_749_, lean_object* v_inst_750_){
_start:
{
lean_object* v___f_751_; 
v___f_751_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_751_, 0, v_inst_750_);
return v___f_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(uint8_t v_pu_754_, lean_object* v_type_755_, lean_object* v_xs_756_, lean_object* v_ps_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
if (lean_obj_tag(v_type_755_) == 7)
{
lean_object* v_binderType_763_; lean_object* v_body_764_; lean_object* v_d_765_; uint8_t v___x_766_; lean_object* v___x_767_; 
v_binderType_763_ = lean_ctor_get(v_type_755_, 1);
lean_inc_ref(v_binderType_763_);
v_body_764_ = lean_ctor_get(v_type_755_, 2);
lean_inc_ref(v_body_764_);
lean_dec_ref(v_type_755_);
v_d_765_ = lean_expr_instantiate_rev(v_binderType_763_, v_xs_756_);
lean_dec_ref(v_binderType_763_);
v___x_766_ = l_Lean_isMarkedBorrowed(v_d_765_);
v___x_767_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_754_, v_d_765_, v___x_766_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v_fvarId_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref(v___x_767_);
v_fvarId_769_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_fvarId_769_);
v___x_770_ = l_Lean_Expr_fvar___override(v_fvarId_769_);
v___x_771_ = lean_array_push(v_xs_756_, v___x_770_);
v___x_772_ = lean_array_push(v_ps_757_, v_a_768_);
v_type_755_ = v_body_764_;
v_xs_756_ = v___x_771_;
v_ps_757_ = v___x_772_;
goto _start;
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_body_764_);
lean_dec_ref(v_ps_757_);
lean_dec_ref(v_xs_756_);
v_a_774_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_767_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_767_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_type_782_; lean_object* v_type_x27_783_; uint8_t v___x_784_; 
v_type_782_ = lean_expr_instantiate_rev(v_type_755_, v_xs_756_);
lean_dec_ref(v_xs_756_);
lean_dec_ref(v_type_755_);
lean_inc_ref(v_type_782_);
v_type_x27_783_ = l_Lean_Expr_headBeta(v_type_782_);
v___x_784_ = lean_expr_eqv(v_type_x27_783_, v_type_782_);
lean_dec_ref(v_type_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
v___x_785_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0));
v_type_755_ = v_type_x27_783_;
v_xs_756_ = v___x_785_;
goto _start;
}
else
{
lean_object* v___x_787_; 
lean_dec_ref(v_type_x27_783_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v_ps_757_);
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___boxed(lean_object* v_pu_788_, lean_object* v_type_789_, lean_object* v_xs_790_, lean_object* v_ps_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
uint8_t v_pu_boxed_797_; lean_object* v_res_798_; 
v_pu_boxed_797_ = lean_unbox(v_pu_788_);
v_res_798_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(v_pu_boxed_797_, v_type_789_, v_xs_790_, v_ps_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams(uint8_t v_pu_799_, lean_object* v_type_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0));
v___x_807_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(v_pu_799_, v_type_800_, v___x_806_, v___x_806_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams___boxed(lean_object* v_pu_808_, lean_object* v_type_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
uint8_t v_pu_boxed_815_; lean_object* v_res_816_; 
v_pu_boxed_815_ = lean_unbox(v_pu_808_);
v_res_816_ = l_Lean_Compiler_LCNF_mkNewParams(v_pu_boxed_815_, v_type_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_816_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object* v_type_817_, lean_object* v_params_818_){
_start:
{
lean_object* v_typeArity_819_; lean_object* v_valueArity_820_; uint8_t v___x_821_; 
v_typeArity_819_ = l_Lean_Compiler_LCNF_getArrowArity(v_type_817_);
v_valueArity_820_ = lean_array_get_size(v_params_818_);
v___x_821_ = lean_nat_dec_lt(v_valueArity_820_, v_typeArity_819_);
lean_dec(v_typeArity_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isEtaExpandCandidateCore___boxed(lean_object* v_type_822_, lean_object* v_params_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_822_, v_params_823_);
lean_dec_ref(v_params_823_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(lean_object* v_decl_826_){
_start:
{
lean_object* v_params_827_; lean_object* v_type_828_; uint8_t v___x_829_; 
v_params_827_ = lean_ctor_get(v_decl_826_, 2);
lean_inc_ref(v_params_827_);
v_type_828_ = lean_ctor_get(v_decl_826_, 3);
lean_inc_ref(v_type_828_);
lean_dec_ref(v_decl_826_);
v___x_829_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_828_, v_params_827_);
lean_dec_ref(v_params_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate___boxed(lean_object* v_decl_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(v_decl_830_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0(lean_object* v___x_836_, uint8_t v___x_837_, lean_object* v_fvarId_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_844_, 0, v_fvarId_838_);
lean_ctor_set(v___x_844_, 1, v___x_836_);
v___x_845_ = ((lean_object*)(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1));
v___x_846_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_837_, v___x_844_, v___x_845_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_857_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_857_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_857_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_857_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_fvarId_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v_fvarId_851_ = lean_ctor_get(v_a_847_, 0);
lean_inc(v_fvarId_851_);
v___x_852_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_852_, 0, v_fvarId_851_);
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v_a_847_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_853_);
v___x_855_ = v___x_849_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_846_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_846_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed(lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v_fvarId_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v___x_901__boxed_874_; lean_object* v_res_875_; 
v___x_901__boxed_874_ = lean_unbox(v___x_867_);
v_res_875_ = l_Lean_Compiler_LCNF_etaExpandCore___lam__0(v___x_866_, v___x_901__boxed_874_, v_fvarId_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(size_t v_sz_876_, size_t v_i_877_, lean_object* v_bs_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_lt(v_i_877_, v_sz_876_);
if (v___x_879_ == 0)
{
return v_bs_878_;
}
else
{
lean_object* v_v_880_; lean_object* v_fvarId_881_; lean_object* v___x_882_; lean_object* v_bs_x27_883_; lean_object* v___x_884_; size_t v___x_885_; size_t v___x_886_; lean_object* v___x_887_; 
v_v_880_ = lean_array_uget_borrowed(v_bs_878_, v_i_877_);
v_fvarId_881_ = lean_ctor_get(v_v_880_, 0);
lean_inc(v_fvarId_881_);
v___x_882_ = lean_unsigned_to_nat(0u);
v_bs_x27_883_ = lean_array_uset(v_bs_878_, v_i_877_, v___x_882_);
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v_fvarId_881_);
v___x_885_ = ((size_t)1ULL);
v___x_886_ = lean_usize_add(v_i_877_, v___x_885_);
v___x_887_ = lean_array_uset(v_bs_x27_883_, v_i_877_, v___x_884_);
v_i_877_ = v___x_886_;
v_bs_878_ = v___x_887_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1___boxed(lean_object* v_sz_889_, lean_object* v_i_890_, lean_object* v_bs_891_){
_start:
{
size_t v_sz_boxed_892_; size_t v_i_boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_889_);
lean_dec(v_sz_889_);
v_i_boxed_893_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_boxed_892_, v_i_boxed_893_, v_bs_891_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(size_t v_sz_895_, size_t v_i_896_, lean_object* v_bs_897_){
_start:
{
uint8_t v___x_898_; 
v___x_898_ = lean_usize_dec_lt(v_i_896_, v_sz_895_);
if (v___x_898_ == 0)
{
return v_bs_897_;
}
else
{
lean_object* v_v_899_; lean_object* v_fvarId_900_; lean_object* v___x_901_; lean_object* v_bs_x27_902_; lean_object* v___x_903_; size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v_v_899_ = lean_array_uget_borrowed(v_bs_897_, v_i_896_);
v_fvarId_900_ = lean_ctor_get(v_v_899_, 0);
lean_inc(v_fvarId_900_);
v___x_901_ = lean_unsigned_to_nat(0u);
v_bs_x27_902_ = lean_array_uset(v_bs_897_, v_i_896_, v___x_901_);
v___x_903_ = l_Lean_mkFVar(v_fvarId_900_);
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_add(v_i_896_, v___x_904_);
v___x_906_ = lean_array_uset(v_bs_x27_902_, v_i_896_, v___x_903_);
v_i_896_ = v___x_905_;
v_bs_897_ = v___x_906_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0___boxed(lean_object* v_sz_908_, lean_object* v_i_909_, lean_object* v_bs_910_){
_start:
{
size_t v_sz_boxed_911_; size_t v_i_boxed_912_; lean_object* v_res_913_; 
v_sz_boxed_911_ = lean_unbox_usize(v_sz_908_);
lean_dec(v_sz_908_);
v_i_boxed_912_ = lean_unbox_usize(v_i_909_);
lean_dec(v_i_909_);
v_res_913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_boxed_911_, v_i_boxed_912_, v_bs_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore(lean_object* v_type_914_, lean_object* v_params_915_, lean_object* v_value_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
size_t v_sz_922_; size_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_sz_922_ = lean_array_size(v_params_915_);
v___x_923_ = ((size_t)0ULL);
lean_inc_ref(v_params_915_);
v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_922_, v___x_923_, v_params_915_);
v___x_925_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_914_, v___x_924_, v_a_919_, v_a_920_);
lean_dec_ref(v___x_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; uint8_t v___x_927_; lean_object* v___x_928_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref(v___x_925_);
v___x_927_ = 0;
v___x_928_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_927_, v_a_926_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; size_t v_sz_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___f_934_; lean_object* v___x_935_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = l_Array_append___redArg(v_params_915_, v_a_929_);
v_sz_931_ = lean_array_size(v_a_929_);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_931_, v___x_923_, v_a_929_);
v___x_933_ = lean_box(v___x_927_);
v___f_934_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed), 8, 2);
lean_closure_set(v___f_934_, 0, v___x_932_);
lean_closure_set(v___f_934_, 1, v___x_933_);
v___x_935_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___x_927_, v_value_916_, v___f_934_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_944_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_930_);
lean_ctor_set(v___x_940_, 1, v_a_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec_ref(v___x_930_);
v_a_945_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_935_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_935_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v_value_916_);
lean_dec_ref(v_params_915_);
v_a_953_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_928_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_928_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v_value_916_);
lean_dec_ref(v_params_915_);
v_a_961_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_925_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_925_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___boxed(lean_object* v_type_969_, lean_object* v_params_970_, lean_object* v_value_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Compiler_LCNF_etaExpandCore(v_type_969_, v_params_970_, v_value_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f(lean_object* v_type_978_, lean_object* v_params_979_, lean_object* v_value_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
uint8_t v___x_986_; 
lean_inc_ref(v_type_978_);
v___x_986_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_978_, v_params_979_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec_ref(v_value_980_);
lean_dec_ref(v_params_979_);
lean_dec_ref(v_type_978_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Compiler_LCNF_etaExpandCore(v_type_978_, v_params_979_, v_value_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_998_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_998_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_a_990_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
v_a_999_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_989_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_989_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f___boxed(lean_object* v_type_1007_, lean_object* v_params_1008_, lean_object* v_value_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1007_, v_params_1008_, v_value_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object* v_decl_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_params_1022_; lean_object* v_type_1023_; lean_object* v_value_1024_; lean_object* v___x_1025_; 
v_params_1022_ = lean_ctor_get(v_decl_1016_, 2);
v_type_1023_ = lean_ctor_get(v_decl_1016_, 3);
v_value_1024_ = lean_ctor_get(v_decl_1016_, 4);
lean_inc_ref(v_value_1024_);
lean_inc_ref(v_params_1022_);
lean_inc_ref(v_type_1023_);
v___x_1025_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1023_, v_params_1022_, v_value_1024_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1038_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1038_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1038_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
if (lean_obj_tag(v_a_1026_) == 1)
{
lean_object* v_val_1030_; lean_object* v_fst_1031_; lean_object* v_snd_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; 
lean_inc_ref(v_type_1023_);
lean_del_object(v___x_1028_);
v_val_1030_ = lean_ctor_get(v_a_1026_, 0);
lean_inc(v_val_1030_);
lean_dec_ref(v_a_1026_);
v_fst_1031_ = lean_ctor_get(v_val_1030_, 0);
lean_inc(v_fst_1031_);
v_snd_1032_ = lean_ctor_get(v_val_1030_, 1);
lean_inc(v_snd_1032_);
lean_dec(v_val_1030_);
v___x_1033_ = 0;
v___x_1034_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1033_, v_decl_1016_, v_type_1023_, v_fst_1031_, v_snd_1032_, v_a_1018_);
return v___x_1034_;
}
else
{
lean_object* v___x_1036_; 
lean_dec(v_a_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v_decl_1016_);
v___x_1036_ = v___x_1028_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_decl_1016_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v_decl_1016_);
v_a_1039_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1025_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1025_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand___boxed(lean_object* v_decl_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_decl_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object* v_decl_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_value_1060_; 
v_value_1060_ = lean_ctor_get(v_decl_1054_, 1);
lean_inc_ref(v_value_1060_);
if (lean_obj_tag(v_value_1060_) == 0)
{
lean_object* v_toSignature_1061_; uint8_t v_recursive_1062_; lean_object* v_inlineAttr_x3f_1063_; lean_object* v_code_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1116_; 
v_toSignature_1061_ = lean_ctor_get(v_decl_1054_, 0);
lean_inc_ref(v_toSignature_1061_);
v_recursive_1062_ = lean_ctor_get_uint8(v_decl_1054_, sizeof(void*)*3);
v_inlineAttr_x3f_1063_ = lean_ctor_get(v_decl_1054_, 2);
v_code_1064_ = lean_ctor_get(v_value_1060_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_value_1060_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1066_ = v_value_1060_;
v_isShared_1067_ = v_isSharedCheck_1116_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_code_1064_);
lean_dec(v_value_1060_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1116_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_name_1068_; lean_object* v_levelParams_1069_; lean_object* v_type_1070_; lean_object* v_params_1071_; uint8_t v_safe_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1115_; 
v_name_1068_ = lean_ctor_get(v_toSignature_1061_, 0);
v_levelParams_1069_ = lean_ctor_get(v_toSignature_1061_, 1);
v_type_1070_ = lean_ctor_get(v_toSignature_1061_, 2);
v_params_1071_ = lean_ctor_get(v_toSignature_1061_, 3);
v_safe_1072_ = lean_ctor_get_uint8(v_toSignature_1061_, sizeof(void*)*4);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_toSignature_1061_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1074_ = v_toSignature_1061_;
v_isShared_1075_ = v_isSharedCheck_1115_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_params_1071_);
lean_inc(v_type_1070_);
lean_inc(v_levelParams_1069_);
lean_inc(v_name_1068_);
lean_dec(v_toSignature_1061_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1115_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; 
lean_inc_ref(v_type_1070_);
v___x_1076_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1070_, v_params_1071_, v_code_1064_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1106_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1106_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1106_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
if (lean_obj_tag(v_a_1077_) == 1)
{
lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1099_; 
lean_inc(v_inlineAttr_x3f_1063_);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_decl_1054_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; lean_object* v_unused_1101_; lean_object* v_unused_1102_; 
v_unused_1100_ = lean_ctor_get(v_decl_1054_, 2);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_decl_1054_, 1);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_decl_1054_, 0);
lean_dec(v_unused_1102_);
v___x_1082_ = v_decl_1054_;
v_isShared_1083_ = v_isSharedCheck_1099_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v_decl_1054_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1099_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_val_1084_; lean_object* v_fst_1085_; lean_object* v_snd_1086_; lean_object* v___x_1088_; 
v_val_1084_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_val_1084_);
lean_dec_ref(v_a_1077_);
v_fst_1085_ = lean_ctor_get(v_val_1084_, 0);
lean_inc(v_fst_1085_);
v_snd_1086_ = lean_ctor_get(v_val_1084_, 1);
lean_inc(v_snd_1086_);
lean_dec(v_val_1084_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 3, v_fst_1085_);
v___x_1088_ = v___x_1074_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_name_1068_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_levelParams_1069_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_type_1070_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_fst_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1098_, sizeof(void*)*4, v_safe_1072_);
v___x_1088_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v_snd_1086_);
v___x_1090_ = v___x_1066_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_snd_1086_);
v___x_1090_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1092_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v___x_1090_);
lean_ctor_set(v___x_1082_, 0, v___x_1088_);
v___x_1092_ = v___x_1082_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_inlineAttr_x3f_1063_);
lean_ctor_set_uint8(v_reuseFailAlloc_1096_, sizeof(void*)*3, v_recursive_1062_);
v___x_1092_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1094_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1092_);
v___x_1094_ = v___x_1079_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
}
else
{
lean_object* v___x_1104_; 
lean_dec(v_a_1077_);
lean_del_object(v___x_1074_);
lean_dec_ref(v_type_1070_);
lean_dec(v_levelParams_1069_);
lean_dec(v_name_1068_);
lean_del_object(v___x_1066_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_decl_1054_);
v___x_1104_ = v___x_1079_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_decl_1054_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1074_);
lean_dec_ref(v_type_1070_);
lean_dec(v_levelParams_1069_);
lean_dec(v_name_1068_);
lean_del_object(v___x_1066_);
lean_dec_ref(v_decl_1054_);
v_a_1107_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1076_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1076_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
else
{
lean_object* v___x_1117_; 
lean_dec_ref(v_value_1060_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_decl_1054_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand___boxed(lean_object* v_decl_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1124_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Compiler_LCNF_Bind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Bind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Bind(builtin);
}
#ifdef __cplusplus
}
#endif
