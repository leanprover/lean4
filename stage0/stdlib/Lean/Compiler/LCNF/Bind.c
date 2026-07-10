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
uint8_t lean_bool_not(uint8_t);
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
lean_dec_ref_known(v___x_172_, 1);
lean_inc_ref(v_params_170_);
v___x_174_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_120_, v_params_170_, v_a_173_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
v___x_176_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_120_, v_decl_165_, v_a_175_, v_params_170_, v_a_173_, v_a_125_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_fvarId_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
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
lean_dec_ref_known(v_c_122_, 2);
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
lean_dec_ref_known(v___x_242_, 1);
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
lean_dec_ref_known(v___x_276_, 1);
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
lean_dec_ref_known(v_c_122_, 1);
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
lean_dec_ref_known(v___x_303_, 1);
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
lean_dec_ref_known(v___x_306_, 1);
v___x_308_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_120_, v_a_307_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_308_, 1);
v___x_310_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_120_, v_a_307_, v_a_125_);
lean_dec(v_a_307_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v___x_311_; 
lean_dec_ref_known(v___x_310_, 1);
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
lean_dec_ref_known(v_c_122_, 4);
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
lean_dec_ref_known(v_c_122_, 4);
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
lean_dec_ref_known(v_c_122_, 6);
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
lean_dec_ref_known(v_c_122_, 3);
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
lean_dec_ref_known(v_c_122_, 3);
return v___x_483_;
}
}
case 12:
{
lean_object* v_fvarId_508_; lean_object* v_n_509_; uint8_t v_check_510_; uint8_t v_persistent_511_; lean_object* v_objs_x3f_512_; lean_object* v_k_513_; lean_object* v___x_514_; 
v_fvarId_508_ = lean_ctor_get(v_c_122_, 0);
v_n_509_ = lean_ctor_get(v_c_122_, 1);
v_check_510_ = lean_ctor_get_uint8(v_c_122_, sizeof(void*)*4);
v_persistent_511_ = lean_ctor_get_uint8(v_c_122_, sizeof(void*)*4 + 1);
v_objs_x3f_512_ = lean_ctor_get(v_c_122_, 2);
v_k_513_ = lean_ctor_get(v_c_122_, 3);
lean_inc_ref(v_k_513_);
v___x_514_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_513_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_539_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_539_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_539_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_539_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
size_t v___x_519_; size_t v___x_520_; uint8_t v___x_521_; 
v___x_519_ = lean_ptr_addr(v_k_513_);
v___x_520_ = lean_ptr_addr(v_a_515_);
v___x_521_ = lean_usize_dec_eq(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_531_; 
lean_inc(v_objs_x3f_512_);
lean_inc(v_n_509_);
lean_inc(v_fvarId_508_);
v_isSharedCheck_531_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; lean_object* v_unused_533_; lean_object* v_unused_534_; lean_object* v_unused_535_; 
v_unused_532_ = lean_ctor_get(v_c_122_, 3);
lean_dec(v_unused_532_);
v_unused_533_ = lean_ctor_get(v_c_122_, 2);
lean_dec(v_unused_533_);
v_unused_534_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_534_);
v_unused_535_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_535_);
v___x_523_ = v_c_122_;
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
else
{
lean_dec(v_c_122_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 3, v_a_515_);
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fvarId_508_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_n_509_);
lean_ctor_set(v_reuseFailAlloc_530_, 2, v_objs_x3f_512_);
lean_ctor_set(v_reuseFailAlloc_530_, 3, v_a_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*4, v_check_510_);
lean_ctor_set_uint8(v_reuseFailAlloc_530_, sizeof(void*)*4 + 1, v_persistent_511_);
v___x_526_ = v_reuseFailAlloc_530_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_526_);
v___x_528_ = v___x_517_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v___x_537_; 
lean_dec(v_a_515_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v_c_122_);
v___x_537_ = v___x_517_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_c_122_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_122_, 4);
return v___x_514_;
}
}
default: 
{
lean_object* v_fvarId_540_; lean_object* v_k_541_; lean_object* v___x_542_; 
v_fvarId_540_ = lean_ctor_get(v_c_122_, 0);
v_k_541_ = lean_ctor_get(v_c_122_, 1);
lean_inc_ref(v_k_541_);
v___x_542_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_120_, v_f_121_, v_k_541_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_565_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_565_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_565_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_565_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
size_t v___x_547_; size_t v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_ptr_addr(v_k_541_);
v___x_548_ = lean_ptr_addr(v_a_543_);
v___x_549_ = lean_usize_dec_eq(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_559_; 
lean_inc(v_fvarId_540_);
v_isSharedCheck_559_ = !lean_is_exclusive(v_c_122_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; lean_object* v_unused_561_; 
v_unused_560_ = lean_ctor_get(v_c_122_, 1);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_c_122_, 0);
lean_dec(v_unused_561_);
v___x_551_ = v_c_122_;
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
else
{
lean_dec(v_c_122_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v_a_543_);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_fvarId_540_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_a_543_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_554_);
v___x_556_ = v___x_545_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_object* v___x_563_; 
lean_dec(v_a_543_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v_c_122_);
v___x_563_ = v___x_545_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_c_122_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_122_, 2);
return v___x_542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(uint8_t v_pu_566_, lean_object* v_f_567_, size_t v_sz_568_, size_t v_i_569_, lean_object* v_bs_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_lt(v_i_569_, v_sz_568_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
lean_dec_ref(v_f_567_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v_bs_570_);
return v___x_578_;
}
else
{
lean_object* v_v_579_; lean_object* v___x_580_; lean_object* v_bs_x27_581_; lean_object* v_a_583_; 
v_v_579_ = lean_array_uget(v_bs_570_, v_i_569_);
v___x_580_ = lean_unsigned_to_nat(0u);
v_bs_x27_581_ = lean_array_uset(v_bs_570_, v_i_569_, v___x_580_);
switch(lean_obj_tag(v_v_579_))
{
case 0:
{
lean_object* v_ctorName_588_; lean_object* v_params_589_; lean_object* v_code_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_607_; 
v_ctorName_588_ = lean_ctor_get(v_v_579_, 0);
v_params_589_ = lean_ctor_get(v_v_579_, 1);
v_code_590_ = lean_ctor_get(v_v_579_, 2);
v_isSharedCheck_607_ = !lean_is_exclusive(v_v_579_);
if (v_isSharedCheck_607_ == 0)
{
v___x_592_ = v_v_579_;
v_isShared_593_ = v_isSharedCheck_607_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_code_590_);
lean_inc(v_params_589_);
lean_inc(v_ctorName_588_);
lean_dec(v_v_579_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_607_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; 
lean_inc_ref(v_f_567_);
v___x_594_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_566_, v_f_567_, v_code_590_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 2, v_a_595_);
v___x_597_ = v___x_592_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_ctorName_588_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_params_589_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_a_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
v_a_583_ = v___x_597_;
goto v___jp_582_;
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_del_object(v___x_592_);
lean_dec_ref(v_params_589_);
lean_dec(v_ctorName_588_);
lean_dec_ref(v_bs_x27_581_);
lean_dec_ref(v_f_567_);
v_a_599_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_594_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_594_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
case 1:
{
lean_object* v_info_608_; lean_object* v_code_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_626_; 
v_info_608_ = lean_ctor_get(v_v_579_, 0);
v_code_609_ = lean_ctor_get(v_v_579_, 1);
v_isSharedCheck_626_ = !lean_is_exclusive(v_v_579_);
if (v_isSharedCheck_626_ == 0)
{
v___x_611_ = v_v_579_;
v_isShared_612_ = v_isSharedCheck_626_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_code_609_);
lean_inc(v_info_608_);
lean_dec(v_v_579_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_626_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; 
lean_inc_ref(v_f_567_);
v___x_613_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_566_, v_f_567_, v_code_609_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v_a_614_);
v___x_616_ = v___x_611_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_info_608_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_a_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
v_a_583_ = v___x_616_;
goto v___jp_582_;
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_del_object(v___x_611_);
lean_dec_ref(v_info_608_);
lean_dec_ref(v_bs_x27_581_);
lean_dec_ref(v_f_567_);
v_a_618_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_613_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_613_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
default: 
{
lean_object* v_code_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_644_; 
v_code_627_ = lean_ctor_get(v_v_579_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_v_579_);
if (v_isSharedCheck_644_ == 0)
{
v___x_629_ = v_v_579_;
v_isShared_630_ = v_isSharedCheck_644_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_code_627_);
lean_dec(v_v_579_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_644_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; 
lean_inc_ref(v_f_567_);
v___x_631_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_566_, v_f_567_, v_code_627_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v_a_632_);
v___x_634_ = v___x_629_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
v_a_583_ = v___x_634_;
goto v___jp_582_;
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_del_object(v___x_629_);
lean_dec_ref(v_bs_x27_581_);
lean_dec_ref(v_f_567_);
v_a_636_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_631_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_631_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
v___jp_582_:
{
size_t v___x_584_; size_t v___x_585_; lean_object* v___x_586_; 
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_add(v_i_569_, v___x_584_);
v___x_586_ = lean_array_uset(v_bs_x27_581_, v_i_569_, v_a_583_);
v_i_569_ = v___x_585_;
v_bs_570_ = v___x_586_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2___boxed(lean_object* v_pu_645_, lean_object* v_f_646_, lean_object* v_sz_647_, lean_object* v_i_648_, lean_object* v_bs_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
uint8_t v_pu_boxed_656_; size_t v_sz_boxed_657_; size_t v_i_boxed_658_; lean_object* v_res_659_; 
v_pu_boxed_656_ = lean_unbox(v_pu_645_);
v_sz_boxed_657_ = lean_unbox_usize(v_sz_647_);
lean_dec(v_sz_647_);
v_i_boxed_658_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(v_pu_boxed_656_, v_f_646_, v_sz_boxed_657_, v_i_boxed_658_, v_bs_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___boxed(lean_object* v_pu_660_, lean_object* v_f_661_, lean_object* v_c_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
uint8_t v_pu_boxed_669_; lean_object* v_res_670_; 
v_pu_boxed_669_ = lean_unbox(v_pu_660_);
v_res_670_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_boxed_669_, v_f_661_, v_c_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
return v_res_670_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(lean_object* v_00_u03b2_671_, lean_object* v_k_672_, lean_object* v_t_673_){
_start:
{
uint8_t v___x_674_; 
v___x_674_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_k_672_, v_t_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___boxed(lean_object* v_00_u03b2_675_, lean_object* v_k_676_, lean_object* v_t_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(v_00_u03b2_675_, v_k_676_, v_t_677_);
lean_dec(v_t_677_);
lean_dec(v_k_676_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(uint8_t v_pu_680_, lean_object* v_c_681_, lean_object* v_f_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_box(1);
v___x_689_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_680_, v_f_682_, v_c_681_, v___x_688_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind___boxed(lean_object* v_pu_690_, lean_object* v_c_691_, lean_object* v_f_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
uint8_t v_pu_boxed_698_; lean_object* v_res_699_; 
v_pu_boxed_698_ = lean_unbox(v_pu_690_);
v_res_699_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v_pu_boxed_698_, v_c_691_, v_f_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0(lean_object* v_f_702_, lean_object* v_ctx_703_, lean_object* v_fvarId_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_apply_2(v_f_702_, v_fvarId_704_, v_ctx_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(lean_object* v_inst_706_, uint8_t v_pu_707_, lean_object* v_c_708_, lean_object* v_f_709_, lean_object* v_ctx_710_){
_start:
{
lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_711_, 0, v_f_709_);
lean_closure_set(v___f_711_, 1, v_ctx_710_);
v___x_712_ = lean_box(v_pu_707_);
v___x_713_ = lean_apply_3(v_inst_706_, v___x_712_, v_c_708_, v___f_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed(lean_object* v_inst_714_, lean_object* v_pu_715_, lean_object* v_c_716_, lean_object* v_f_717_, lean_object* v_ctx_718_){
_start:
{
uint8_t v_pu_21__boxed_719_; lean_object* v_res_720_; 
v_pu_21__boxed_719_ = lean_unbox(v_pu_715_);
v_res_720_ = l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(v_inst_714_, v_pu_21__boxed_719_, v_c_716_, v_f_717_, v_ctx_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg(lean_object* v_inst_721_){
_start:
{
lean_object* v___f_722_; 
v___f_722_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_722_, 0, v_inst_721_);
return v___f_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT(lean_object* v_m_723_, lean_object* v_00_u03c1_724_, lean_object* v_inst_725_){
_start:
{
lean_object* v___f_726_; 
v___f_726_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_726_, 0, v_inst_725_);
return v___f_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0(lean_object* v_f_727_, lean_object* v_sref_728_, lean_object* v_fvarId_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_apply_2(v_f_727_, v_fvarId_729_, v_sref_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(lean_object* v_inst_731_, uint8_t v_pu_732_, lean_object* v_c_733_, lean_object* v_f_734_, lean_object* v_sref_735_){
_start:
{
lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0), 3, 2);
lean_closure_set(v___f_736_, 0, v_f_734_);
lean_closure_set(v___f_736_, 1, v_sref_735_);
v___x_737_ = lean_box(v_pu_732_);
v___x_738_ = lean_apply_3(v_inst_731_, v___x_737_, v_c_733_, v___f_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed(lean_object* v_inst_739_, lean_object* v_pu_740_, lean_object* v_c_741_, lean_object* v_f_742_, lean_object* v_sref_743_){
_start:
{
uint8_t v_pu_23__boxed_744_; lean_object* v_res_745_; 
v_pu_23__boxed_744_ = lean_unbox(v_pu_740_);
v_res_745_ = l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(v_inst_739_, v_pu_23__boxed_744_, v_c_741_, v_f_742_, v_sref_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg(lean_object* v_inst_746_){
_start:
{
lean_object* v___f_747_; 
v___f_747_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_747_, 0, v_inst_746_);
return v___f_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld(lean_object* v_00_u03c9_748_, lean_object* v_m_749_, lean_object* v_00_u03c3_750_, lean_object* v_inst_751_, lean_object* v_inst_752_){
_start:
{
lean_object* v___f_753_; 
v___f_753_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_753_, 0, v_inst_752_);
return v___f_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(uint8_t v_pu_756_, lean_object* v_type_757_, lean_object* v_xs_758_, lean_object* v_ps_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
if (lean_obj_tag(v_type_757_) == 7)
{
lean_object* v_binderType_765_; lean_object* v_body_766_; lean_object* v_d_767_; uint8_t v___x_768_; lean_object* v___x_769_; 
v_binderType_765_ = lean_ctor_get(v_type_757_, 1);
lean_inc_ref(v_binderType_765_);
v_body_766_ = lean_ctor_get(v_type_757_, 2);
lean_inc_ref(v_body_766_);
lean_dec_ref_known(v_type_757_, 3);
v_d_767_ = lean_expr_instantiate_rev(v_binderType_765_, v_xs_758_);
lean_dec_ref(v_binderType_765_);
v___x_768_ = l_Lean_isMarkedBorrowed(v_d_767_);
v___x_769_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_756_, v_d_767_, v___x_768_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v_fvarId_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref_known(v___x_769_, 1);
v_fvarId_771_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_fvarId_771_);
v___x_772_ = l_Lean_Expr_fvar___override(v_fvarId_771_);
v___x_773_ = lean_array_push(v_xs_758_, v___x_772_);
v___x_774_ = lean_array_push(v_ps_759_, v_a_770_);
v_type_757_ = v_body_766_;
v_xs_758_ = v___x_773_;
v_ps_759_ = v___x_774_;
goto _start;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_body_766_);
lean_dec_ref(v_ps_759_);
lean_dec_ref(v_xs_758_);
v_a_776_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_769_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_769_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_type_784_; lean_object* v_type_x27_785_; uint8_t v___x_786_; uint8_t v___x_787_; 
v_type_784_ = lean_expr_instantiate_rev(v_type_757_, v_xs_758_);
lean_dec_ref(v_xs_758_);
lean_dec_ref(v_type_757_);
lean_inc_ref(v_type_784_);
v_type_x27_785_ = l_Lean_Expr_headBeta(v_type_784_);
v___x_786_ = lean_expr_eqv(v_type_x27_785_, v_type_784_);
lean_dec_ref(v_type_784_);
v___x_787_ = lean_bool_not(v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec_ref(v_type_x27_785_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_ps_759_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; 
v___x_789_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0));
v_type_757_ = v_type_x27_785_;
v_xs_758_ = v___x_789_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___boxed(lean_object* v_pu_791_, lean_object* v_type_792_, lean_object* v_xs_793_, lean_object* v_ps_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
uint8_t v_pu_boxed_800_; lean_object* v_res_801_; 
v_pu_boxed_800_ = lean_unbox(v_pu_791_);
v_res_801_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(v_pu_boxed_800_, v_type_792_, v_xs_793_, v_ps_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams(uint8_t v_pu_802_, lean_object* v_type_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0));
v___x_810_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(v_pu_802_, v_type_803_, v___x_809_, v___x_809_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams___boxed(lean_object* v_pu_811_, lean_object* v_type_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
uint8_t v_pu_boxed_818_; lean_object* v_res_819_; 
v_pu_boxed_818_ = lean_unbox(v_pu_811_);
v_res_819_ = l_Lean_Compiler_LCNF_mkNewParams(v_pu_boxed_818_, v_type_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_819_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object* v_type_820_, lean_object* v_params_821_){
_start:
{
lean_object* v_typeArity_822_; lean_object* v_valueArity_823_; uint8_t v___x_824_; 
v_typeArity_822_ = l_Lean_Compiler_LCNF_getArrowArity(v_type_820_);
v_valueArity_823_ = lean_array_get_size(v_params_821_);
v___x_824_ = lean_nat_dec_lt(v_valueArity_823_, v_typeArity_822_);
lean_dec(v_typeArity_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isEtaExpandCandidateCore___boxed(lean_object* v_type_825_, lean_object* v_params_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_825_, v_params_826_);
lean_dec_ref(v_params_826_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(lean_object* v_decl_829_){
_start:
{
lean_object* v_params_830_; lean_object* v_type_831_; uint8_t v___x_832_; 
v_params_830_ = lean_ctor_get(v_decl_829_, 2);
lean_inc_ref(v_params_830_);
v_type_831_ = lean_ctor_get(v_decl_829_, 3);
lean_inc_ref(v_type_831_);
lean_dec_ref(v_decl_829_);
v___x_832_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_831_, v_params_830_);
lean_dec_ref(v_params_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate___boxed(lean_object* v_decl_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(v_decl_833_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0(lean_object* v___x_839_, uint8_t v___x_840_, lean_object* v_fvarId_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_847_, 0, v_fvarId_841_);
lean_ctor_set(v___x_847_, 1, v___x_839_);
v___x_848_ = ((lean_object*)(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1));
v___x_849_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_840_, v___x_847_, v___x_848_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_860_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_fvarId_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v_fvarId_854_ = lean_ctor_get(v_a_850_, 0);
lean_inc(v_fvarId_854_);
v___x_855_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_855_, 0, v_fvarId_854_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_a_850_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_856_);
v___x_858_ = v___x_852_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_849_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_849_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed(lean_object* v___x_869_, lean_object* v___x_870_, lean_object* v_fvarId_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v___x_903__boxed_877_; lean_object* v_res_878_; 
v___x_903__boxed_877_ = lean_unbox(v___x_870_);
v_res_878_ = l_Lean_Compiler_LCNF_etaExpandCore___lam__0(v___x_869_, v___x_903__boxed_877_, v_fvarId_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(size_t v_sz_879_, size_t v_i_880_, lean_object* v_bs_881_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = lean_usize_dec_lt(v_i_880_, v_sz_879_);
if (v___x_882_ == 0)
{
return v_bs_881_;
}
else
{
lean_object* v_v_883_; lean_object* v_fvarId_884_; lean_object* v___x_885_; lean_object* v_bs_x27_886_; lean_object* v___x_887_; size_t v___x_888_; size_t v___x_889_; lean_object* v___x_890_; 
v_v_883_ = lean_array_uget_borrowed(v_bs_881_, v_i_880_);
v_fvarId_884_ = lean_ctor_get(v_v_883_, 0);
lean_inc(v_fvarId_884_);
v___x_885_ = lean_unsigned_to_nat(0u);
v_bs_x27_886_ = lean_array_uset(v_bs_881_, v_i_880_, v___x_885_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_fvarId_884_);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_add(v_i_880_, v___x_888_);
v___x_890_ = lean_array_uset(v_bs_x27_886_, v_i_880_, v___x_887_);
v_i_880_ = v___x_889_;
v_bs_881_ = v___x_890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1___boxed(lean_object* v_sz_892_, lean_object* v_i_893_, lean_object* v_bs_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_892_);
lean_dec(v_sz_892_);
v_i_boxed_896_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_boxed_895_, v_i_boxed_896_, v_bs_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(size_t v_sz_898_, size_t v_i_899_, lean_object* v_bs_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_lt(v_i_899_, v_sz_898_);
if (v___x_901_ == 0)
{
return v_bs_900_;
}
else
{
lean_object* v_v_902_; lean_object* v_fvarId_903_; lean_object* v___x_904_; lean_object* v_bs_x27_905_; lean_object* v___x_906_; size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
v_v_902_ = lean_array_uget_borrowed(v_bs_900_, v_i_899_);
v_fvarId_903_ = lean_ctor_get(v_v_902_, 0);
lean_inc(v_fvarId_903_);
v___x_904_ = lean_unsigned_to_nat(0u);
v_bs_x27_905_ = lean_array_uset(v_bs_900_, v_i_899_, v___x_904_);
v___x_906_ = l_Lean_mkFVar(v_fvarId_903_);
v___x_907_ = ((size_t)1ULL);
v___x_908_ = lean_usize_add(v_i_899_, v___x_907_);
v___x_909_ = lean_array_uset(v_bs_x27_905_, v_i_899_, v___x_906_);
v_i_899_ = v___x_908_;
v_bs_900_ = v___x_909_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0___boxed(lean_object* v_sz_911_, lean_object* v_i_912_, lean_object* v_bs_913_){
_start:
{
size_t v_sz_boxed_914_; size_t v_i_boxed_915_; lean_object* v_res_916_; 
v_sz_boxed_914_ = lean_unbox_usize(v_sz_911_);
lean_dec(v_sz_911_);
v_i_boxed_915_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_res_916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_boxed_914_, v_i_boxed_915_, v_bs_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore(lean_object* v_type_917_, lean_object* v_params_918_, lean_object* v_value_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
size_t v_sz_925_; size_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_sz_925_ = lean_array_size(v_params_918_);
v___x_926_ = ((size_t)0ULL);
lean_inc_ref(v_params_918_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_925_, v___x_926_, v_params_918_);
v___x_928_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_917_, v___x_927_, v_a_922_, v_a_923_);
lean_dec_ref(v___x_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = 0;
v___x_931_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_930_, v_a_929_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_933_; size_t v_sz_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___f_937_; lean_object* v___x_938_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = l_Array_append___redArg(v_params_918_, v_a_932_);
v_sz_934_ = lean_array_size(v_a_932_);
v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_934_, v___x_926_, v_a_932_);
v___x_936_ = lean_box(v___x_930_);
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed), 8, 2);
lean_closure_set(v___f_937_, 0, v___x_935_);
lean_closure_set(v___f_937_, 1, v___x_936_);
v___x_938_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___x_930_, v_value_919_, v___f_937_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_933_);
lean_ctor_set(v___x_943_, 1, v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___x_933_);
v_a_948_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_938_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_938_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_value_919_);
lean_dec_ref(v_params_918_);
v_a_956_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_931_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_931_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec_ref(v_value_919_);
lean_dec_ref(v_params_918_);
v_a_964_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_928_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_928_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___boxed(lean_object* v_type_972_, lean_object* v_params_973_, lean_object* v_value_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Compiler_LCNF_etaExpandCore(v_type_972_, v_params_973_, v_value_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f(lean_object* v_type_981_, lean_object* v_params_982_, lean_object* v_value_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
uint8_t v___x_989_; 
lean_inc_ref(v_type_981_);
v___x_989_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_981_, v_params_982_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec_ref(v_value_983_);
lean_dec_ref(v_params_982_);
lean_dec_ref(v_type_981_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Compiler_LCNF_etaExpandCore(v_type_981_, v_params_982_, v_value_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1001_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_997_, 0, v_a_993_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_999_ = v___x_995_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_992_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_992_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f___boxed(lean_object* v_type_1010_, lean_object* v_params_1011_, lean_object* v_value_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1010_, v_params_1011_, v_value_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object* v_decl_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_params_1025_; lean_object* v_type_1026_; lean_object* v_value_1027_; lean_object* v___x_1028_; 
v_params_1025_ = lean_ctor_get(v_decl_1019_, 2);
v_type_1026_ = lean_ctor_get(v_decl_1019_, 3);
v_value_1027_ = lean_ctor_get(v_decl_1019_, 4);
lean_inc_ref(v_value_1027_);
lean_inc_ref(v_params_1025_);
lean_inc_ref(v_type_1026_);
v___x_1028_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1026_, v_params_1025_, v_value_1027_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1041_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1041_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
if (lean_obj_tag(v_a_1029_) == 1)
{
lean_object* v_val_1033_; lean_object* v_fst_1034_; lean_object* v_snd_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; 
lean_inc_ref(v_type_1026_);
lean_del_object(v___x_1031_);
v_val_1033_ = lean_ctor_get(v_a_1029_, 0);
lean_inc(v_val_1033_);
lean_dec_ref_known(v_a_1029_, 1);
v_fst_1034_ = lean_ctor_get(v_val_1033_, 0);
lean_inc(v_fst_1034_);
v_snd_1035_ = lean_ctor_get(v_val_1033_, 1);
lean_inc(v_snd_1035_);
lean_dec(v_val_1033_);
v___x_1036_ = 0;
v___x_1037_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1036_, v_decl_1019_, v_type_1026_, v_fst_1034_, v_snd_1035_, v_a_1021_);
return v___x_1037_;
}
else
{
lean_object* v___x_1039_; 
lean_dec(v_a_1029_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_decl_1019_);
v___x_1039_ = v___x_1031_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_decl_1019_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_decl_1019_);
v_a_1042_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1028_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1028_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand___boxed(lean_object* v_decl_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_decl_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object* v_decl_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_value_1063_; 
v_value_1063_ = lean_ctor_get(v_decl_1057_, 1);
lean_inc_ref(v_value_1063_);
if (lean_obj_tag(v_value_1063_) == 0)
{
lean_object* v_toSignature_1064_; uint8_t v_recursive_1065_; lean_object* v_inlineAttr_x3f_1066_; lean_object* v_code_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1119_; 
v_toSignature_1064_ = lean_ctor_get(v_decl_1057_, 0);
lean_inc_ref(v_toSignature_1064_);
v_recursive_1065_ = lean_ctor_get_uint8(v_decl_1057_, sizeof(void*)*3);
v_inlineAttr_x3f_1066_ = lean_ctor_get(v_decl_1057_, 2);
v_code_1067_ = lean_ctor_get(v_value_1063_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_value_1063_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1069_ = v_value_1063_;
v_isShared_1070_ = v_isSharedCheck_1119_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_code_1067_);
lean_dec(v_value_1063_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1119_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v_name_1071_; lean_object* v_levelParams_1072_; lean_object* v_type_1073_; lean_object* v_params_1074_; uint8_t v_safe_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1118_; 
v_name_1071_ = lean_ctor_get(v_toSignature_1064_, 0);
v_levelParams_1072_ = lean_ctor_get(v_toSignature_1064_, 1);
v_type_1073_ = lean_ctor_get(v_toSignature_1064_, 2);
v_params_1074_ = lean_ctor_get(v_toSignature_1064_, 3);
v_safe_1075_ = lean_ctor_get_uint8(v_toSignature_1064_, sizeof(void*)*4);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_toSignature_1064_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1077_ = v_toSignature_1064_;
v_isShared_1078_ = v_isSharedCheck_1118_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_params_1074_);
lean_inc(v_type_1073_);
lean_inc(v_levelParams_1072_);
lean_inc(v_name_1071_);
lean_dec(v_toSignature_1064_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1118_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; 
lean_inc_ref(v_type_1073_);
v___x_1079_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1073_, v_params_1074_, v_code_1067_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1109_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1109_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1109_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
if (lean_obj_tag(v_a_1080_) == 1)
{
lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1102_; 
lean_inc(v_inlineAttr_x3f_1066_);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_decl_1057_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; lean_object* v_unused_1105_; 
v_unused_1103_ = lean_ctor_get(v_decl_1057_, 2);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_decl_1057_, 1);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v_decl_1057_, 0);
lean_dec(v_unused_1105_);
v___x_1085_ = v_decl_1057_;
v_isShared_1086_ = v_isSharedCheck_1102_;
goto v_resetjp_1084_;
}
else
{
lean_dec(v_decl_1057_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1102_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v_val_1087_; lean_object* v_fst_1088_; lean_object* v_snd_1089_; lean_object* v___x_1091_; 
v_val_1087_ = lean_ctor_get(v_a_1080_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v_a_1080_, 1);
v_fst_1088_ = lean_ctor_get(v_val_1087_, 0);
lean_inc(v_fst_1088_);
v_snd_1089_ = lean_ctor_get(v_val_1087_, 1);
lean_inc(v_snd_1089_);
lean_dec(v_val_1087_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 3, v_fst_1088_);
v___x_1091_ = v___x_1077_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_name_1071_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_levelParams_1072_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_type_1073_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_fst_1088_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*4, v_safe_1075_);
v___x_1091_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v_snd_1089_);
v___x_1093_ = v___x_1069_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_snd_1089_);
v___x_1093_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1095_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 1, v___x_1093_);
lean_ctor_set(v___x_1085_, 0, v___x_1091_);
v___x_1095_ = v___x_1085_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_inlineAttr_x3f_1066_);
lean_ctor_set_uint8(v_reuseFailAlloc_1099_, sizeof(void*)*3, v_recursive_1065_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1095_);
v___x_1097_ = v___x_1082_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
}
else
{
lean_object* v___x_1107_; 
lean_dec(v_a_1080_);
lean_del_object(v___x_1077_);
lean_dec_ref(v_type_1073_);
lean_dec(v_levelParams_1072_);
lean_dec(v_name_1071_);
lean_del_object(v___x_1069_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v_decl_1057_);
v___x_1107_ = v___x_1082_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_decl_1057_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_del_object(v___x_1077_);
lean_dec_ref(v_type_1073_);
lean_dec(v_levelParams_1072_);
lean_dec(v_name_1071_);
lean_del_object(v___x_1069_);
lean_dec_ref(v_decl_1057_);
v_a_1110_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1079_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1079_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
else
{
lean_object* v___x_1120_; 
lean_dec_ref_known(v_value_1063_, 1);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_decl_1057_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand___boxed(lean_object* v_decl_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1127_;
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
