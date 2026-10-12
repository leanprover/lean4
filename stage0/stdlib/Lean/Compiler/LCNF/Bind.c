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
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
static const lean_string_object l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "`Code.bind` failed, it contains an out-of-scope join point"};
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
lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg(uint8_t v_pu_1_, lean_object* v_inst_2_, lean_object* v_c_3_, lean_object* v_f_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(v_pu_1_);
v___x_6_ = lean_apply_3(v_inst_2_, v___x_5_, v_c_3_, v_f_4_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_bind___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1_ = stack[0].m_num;
lean_object* v_inst_2_ = stack[1].m_obj;
lean_object* v_c_3_ = stack[2].m_obj;
lean_object* v_f_4_ = stack[3].m_obj;
lean_object* v_res_7_;
v_res_7_ = l_Lean_Compiler_LCNF_Code_bind___redArg(v_pu_1_, v_inst_2_, v_c_3_, v_f_4_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___redArg___boxed(lean_object* v_pu_8_, lean_object* v_inst_9_, lean_object* v_c_10_, lean_object* v_f_11_){
_start:
{
uint8_t v_pu_boxed_12_; lean_object* v_res_13_; 
v_pu_boxed_12_ = lean_unbox(v_pu_8_);
v_res_13_ = l_Lean_Compiler_LCNF_Code_bind___redArg(v_pu_boxed_12_, v_inst_9_, v_c_10_, v_f_11_);
return v_res_13_;
}
}
lean_object* l_Lean_Compiler_LCNF_Code_bind(lean_object* v_m_14_, uint8_t v_pu_15_, lean_object* v_inst_16_, lean_object* v_c_17_, lean_object* v_f_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_box(v_pu_15_);
v___x_20_ = lean_apply_3(v_inst_16_, v___x_19_, v_c_17_, v_f_18_);
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_bind_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_15_ = stack[1].m_num;
lean_object* v_inst_16_ = stack[2].m_obj;
lean_object* v_c_17_ = stack[3].m_obj;
lean_object* v_f_18_ = stack[4].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Compiler_LCNF_Code_bind(lean_box(0), v_pu_15_, v_inst_16_, v_c_17_, v_f_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_bind___boxed(lean_object* v_m_22_, lean_object* v_pu_23_, lean_object* v_inst_24_, lean_object* v_c_25_, lean_object* v_f_26_){
_start:
{
uint8_t v_pu_boxed_27_; lean_object* v_res_28_; 
v_pu_boxed_27_ = lean_unbox(v_pu_23_);
v_res_28_ = l_Lean_Compiler_LCNF_Code_bind(v_m_22_, v_pu_boxed_27_, v_inst_24_, v_c_25_, v_f_26_);
return v_res_28_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_29_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__0);
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v___x_30_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_32_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_33_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__1);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
lean_ctor_set(v___x_35_, 2, v___x_34_);
lean_ctor_set(v___x_35_, 3, v___x_34_);
lean_ctor_set(v___x_35_, 4, v___x_33_);
lean_ctor_set(v___x_35_, 5, v___x_33_);
lean_ctor_set(v___x_35_, 6, v___x_33_);
lean_ctor_set(v___x_35_, 7, v___x_33_);
lean_ctor_set(v___x_35_, 8, v___x_33_);
lean_ctor_set(v___x_35_, 9, v___x_33_);
lean_ctor_set(v___x_35_, 10, v___x_33_);
lean_ctor_set(v___x_35_, 11, v___x_32_);
return v___x_35_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(lean_object* v_msg_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_ref_42_; lean_object* v___x_43_; lean_object* v_env_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_ref_42_ = lean_ctor_get(v___y_39_, 2);
v___x_43_ = lean_st_ref_get(v___y_40_);
v_env_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_env_44_);
lean_dec(v___x_43_);
v___x_45_ = lean_st_ref_get(v___y_38_);
v___x_46_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_37_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_69_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_69_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_69_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_69_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v_lctx_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_67_; 
v_lctx_51_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v___x_45_, 1);
lean_dec(v_unused_68_);
v___x_53_ = v___x_45_;
v_isShared_54_ = v_isSharedCheck_67_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_lctx_51_);
lean_dec(v___x_45_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_67_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_55_ = lean_unbox(v_a_47_);
lean_dec(v_a_47_);
v___x_56_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_51_, v___x_55_);
lean_dec_ref(v_lctx_51_);
v___x_57_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_39_);
v___x_58_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___closed__2);
v___x_59_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_59_, 0, v_env_44_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
lean_ctor_set(v___x_59_, 2, v___x_56_);
lean_ctor_set(v___x_59_, 3, v___x_57_);
if (v_isShared_54_ == 0)
{
lean_ctor_set_tag(v___x_53_, 3);
lean_ctor_set(v___x_53_, 1, v_msg_36_);
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_61_ = v___x_53_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_msg_36_);
v___x_61_ = v_reuseFailAlloc_66_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_64_; 
lean_inc(v_ref_42_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v_ref_42_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
if (v_isShared_50_ == 0)
{
lean_ctor_set_tag(v___x_49_, 1);
lean_ctor_set(v___x_49_, 0, v___x_62_);
v___x_64_ = v___x_49_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
}
else
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_77_; 
lean_dec(v___x_45_);
lean_dec_ref(v_env_44_);
lean_dec_ref(v_msg_36_);
v_a_70_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_77_ == 0)
{
v___x_72_ = v___x_46_;
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_46_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_77_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_a_70_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_36_ = stack[0].m_obj;
lean_object* v___y_37_ = stack[1].m_obj;
lean_object* v___y_38_ = stack[2].m_obj;
lean_object* v___y_39_ = stack[3].m_obj;
lean_object* v___y_40_ = stack[4].m_obj;
lean_object* v_res_78_;
v_res_78_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v_msg_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg___boxed(lean_object* v_msg_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v_msg_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_85_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(lean_object* v_00_u03b1_86_, lean_object* v_msg_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v_msg_87_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
return v___x_94_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_87_ = stack[1].m_obj;
lean_object* v___y_88_ = stack[2].m_obj;
lean_object* v___y_89_ = stack[3].m_obj;
lean_object* v___y_90_ = stack[4].m_obj;
lean_object* v___y_91_ = stack[5].m_obj;
lean_object* v___y_92_ = stack[6].m_obj;
lean_object* v_res_95_;
v_res_95_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(lean_box(0), v_msg_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___boxed(lean_object* v_00_u03b1_96_, lean_object* v_msg_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1(v_00_u03b1_96_, v_msg_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
return v_res_104_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(lean_object* v_k_105_, lean_object* v_t_106_){
_start:
{
if (lean_obj_tag(v_t_106_) == 0)
{
lean_object* v_k_107_; lean_object* v_l_108_; lean_object* v_r_109_; uint8_t v___x_110_; 
v_k_107_ = lean_ctor_get(v_t_106_, 1);
v_l_108_ = lean_ctor_get(v_t_106_, 3);
v_r_109_ = lean_ctor_get(v_t_106_, 4);
v___x_110_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_105_, v_k_107_);
switch(v___x_110_)
{
case 0:
{
v_t_106_ = v_l_108_;
goto _start;
}
case 1:
{
uint8_t v___x_112_; 
v___x_112_ = 1;
return v___x_112_;
}
default: 
{
v_t_106_ = v_r_109_;
goto _start;
}
}
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 0;
return v___x_114_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_105_ = stack[0].m_obj;
lean_object* v_t_106_ = stack[1].m_obj;
uint8_t v_res_115_;
v_res_115_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_k_105_, v_t_106_);
stack->m_num = v_res_115_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg___boxed(lean_object* v_k_116_, lean_object* v_t_117_){
_start:
{
uint8_t v_res_118_; lean_object* v_r_119_; 
v_res_118_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_k_116_, v_t_117_);
lean_dec(v_t_117_);
lean_dec(v_k_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__0));
v___x_122_ = l_Lean_stringToMessageData(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__2));
v___x_125_ = l_Lean_stringToMessageData(v___x_124_);
return v___x_125_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(uint8_t v_pu_126_, lean_object* v_f_127_, lean_object* v_c_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
switch(lean_obj_tag(v_c_128_))
{
case 0:
{
lean_object* v_decl_135_; lean_object* v_k_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_152_; 
v_decl_135_ = lean_ctor_get(v_c_128_, 0);
v_k_136_ = lean_ctor_get(v_c_128_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_152_ == 0)
{
v___x_138_ = v_c_128_;
v_isShared_139_ = v_isSharedCheck_152_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_k_136_);
lean_inc(v_decl_135_);
lean_dec(v_c_128_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_152_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_136_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_151_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_151_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_151_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_151_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v_a_141_);
v___x_146_ = v___x_138_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_decl_135_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v_a_141_);
v___x_146_ = v_reuseFailAlloc_150_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_148_; 
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_146_);
v___x_148_ = v___x_143_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
else
{
lean_del_object(v___x_138_);
lean_dec_ref(v_decl_135_);
return v___x_140_;
}
}
}
case 1:
{
lean_object* v_decl_153_; lean_object* v_k_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_170_; 
v_decl_153_ = lean_ctor_get(v_c_128_, 0);
v_k_154_ = lean_ctor_get(v_c_128_, 1);
v_isSharedCheck_170_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_170_ == 0)
{
v___x_156_ = v_c_128_;
v_isShared_157_ = v_isSharedCheck_170_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_k_154_);
lean_inc(v_decl_153_);
lean_dec(v_c_128_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_170_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_154_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_169_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_169_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_a_159_);
v___x_164_ = v___x_156_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_decl_153_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_a_159_);
v___x_164_ = v_reuseFailAlloc_168_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_166_; 
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_164_);
v___x_166_ = v___x_161_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_del_object(v___x_156_);
lean_dec_ref(v_decl_153_);
return v___x_158_;
}
}
}
case 2:
{
lean_object* v_decl_171_; lean_object* v_k_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_214_; 
v_decl_171_ = lean_ctor_get(v_c_128_, 0);
v_k_172_ = lean_ctor_get(v_c_128_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_214_ == 0)
{
v___x_174_ = v_c_128_;
v_isShared_175_ = v_isSharedCheck_214_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_k_172_);
lean_inc(v_decl_171_);
lean_dec(v_c_128_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_214_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_params_176_; lean_object* v_value_177_; lean_object* v___x_178_; 
v_params_176_ = lean_ctor_get(v_decl_171_, 2);
lean_inc_ref(v_params_176_);
v_value_177_ = lean_ctor_get(v_decl_171_, 4);
lean_inc_ref(v_value_177_);
lean_inc_ref(v_f_127_);
v___x_178_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_value_177_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc_n(v_a_179_, 2);
lean_dec_ref_known(v___x_178_, 1);
lean_inc_ref(v_params_176_);
v___x_180_ = l_Lean_Compiler_LCNF_Code_inferParamType(v_pu_126_, v_params_176_, v_a_179_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
v___x_182_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v_pu_126_, v_decl_171_, v_a_181_, v_params_176_, v_a_179_, v_a_131_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v_fvarId_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
v_fvarId_184_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_fvarId_184_);
lean_inc(v_a_129_);
v___x_185_ = l_Lean_FVarIdSet_insert(v_a_129_, v_fvarId_184_);
v___x_186_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_172_, v___x_185_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v___x_185_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_197_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_197_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_197_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 1, v_a_187_);
lean_ctor_set(v___x_174_, 0, v_a_183_);
v___x_192_ = v___x_174_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_183_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_a_187_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v___x_192_);
v___x_194_ = v___x_189_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_dec(v_a_183_);
lean_del_object(v___x_174_);
return v___x_186_;
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_del_object(v___x_174_);
lean_dec_ref(v_k_172_);
lean_dec_ref(v_f_127_);
v_a_198_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_182_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_182_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec(v_a_179_);
lean_dec_ref(v_params_176_);
lean_del_object(v___x_174_);
lean_dec_ref(v_k_172_);
lean_dec_ref(v_decl_171_);
lean_dec_ref(v_f_127_);
v_a_206_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_180_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_180_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
lean_dec_ref(v_params_176_);
lean_del_object(v___x_174_);
lean_dec_ref(v_k_172_);
lean_dec_ref(v_decl_171_);
lean_dec_ref(v_f_127_);
return v___x_178_;
}
}
}
case 3:
{
lean_object* v_fvarId_215_; uint8_t v___x_216_; 
lean_dec_ref(v_f_127_);
v_fvarId_215_ = lean_ctor_get(v_c_128_, 0);
v___x_216_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_fvarId_215_, v_a_129_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1, &l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1_once, _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__1);
v___x_218_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v___x_217_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; 
v_unused_226_ = lean_ctor_get(v___x_218_, 0);
lean_dec(v_unused_226_);
v___x_220_ = v___x_218_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_dec(v___x_218_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v_c_128_);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_c_128_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref_known(v_c_128_, 2);
v_a_227_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_218_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_218_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v_c_128_);
return v___x_235_;
}
}
case 4:
{
lean_object* v_cases_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_301_; 
v_cases_236_ = lean_ctor_get(v_c_128_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_301_ == 0)
{
v___x_238_ = v_c_128_;
v_isShared_239_ = v_isSharedCheck_301_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_cases_236_);
lean_dec(v_c_128_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_301_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_typeName_240_; lean_object* v_discr_241_; lean_object* v_alts_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_299_; 
v_typeName_240_ = lean_ctor_get(v_cases_236_, 0);
v_discr_241_ = lean_ctor_get(v_cases_236_, 2);
v_alts_242_ = lean_ctor_get(v_cases_236_, 3);
v_isSharedCheck_299_ = !lean_is_exclusive(v_cases_236_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v_cases_236_, 1);
lean_dec(v_unused_300_);
v___x_244_ = v_cases_236_;
v_isShared_245_ = v_isSharedCheck_299_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_alts_242_);
lean_inc(v_discr_241_);
lean_inc(v_typeName_240_);
lean_dec(v_cases_236_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_299_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
size_t v_sz_246_; size_t v___x_247_; lean_object* v___x_248_; 
v_sz_246_ = lean_array_size(v_alts_242_);
v___x_247_ = ((size_t)0ULL);
v___x_248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(v_pu_126_, v_f_127_, v_sz_246_, v___x_247_, v_alts_242_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_248_, 1);
v___x_278_ = lean_array_get_size(v_a_249_);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_nat_dec_eq(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
v___y_251_ = v_a_130_;
v___y_252_ = v_a_131_;
v___y_253_ = v_a_132_;
v___y_254_ = v_a_133_;
goto v___jp_250_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3, &l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___closed__3);
v___x_282_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__1___redArg(v___x_281_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_dec_ref_known(v___x_282_, 1);
v___y_251_ = v_a_130_;
v___y_252_ = v_a_131_;
v___y_253_ = v_a_132_;
v___y_254_ = v_a_133_;
goto v___jp_250_;
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec(v_a_249_);
lean_del_object(v___x_244_);
lean_dec(v_discr_241_);
lean_dec(v_typeName_240_);
lean_del_object(v___x_238_);
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
v___jp_250_:
{
lean_object* v___x_255_; 
lean_inc(v_a_249_);
v___x_255_ = l_Lean_Compiler_LCNF_mkCasesResultType(v_pu_126_, v_a_249_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_269_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_269_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_269_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_269_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 3, v_a_249_);
lean_ctor_set(v___x_244_, 1, v_a_256_);
v___x_261_ = v___x_244_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_typeName_240_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_a_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_discr_241_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_a_249_);
v___x_261_ = v_reuseFailAlloc_268_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_263_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_261_);
v___x_263_ = v___x_238_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_267_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_265_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_263_);
v___x_265_ = v___x_258_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_a_249_);
lean_del_object(v___x_244_);
lean_dec(v_discr_241_);
lean_dec(v_typeName_240_);
lean_del_object(v___x_238_);
v_a_270_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_255_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_255_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_del_object(v___x_244_);
lean_dec(v_discr_241_);
lean_dec(v_typeName_240_);
lean_del_object(v___x_238_);
v_a_291_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_248_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_248_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_302_; lean_object* v___x_303_; 
v_fvarId_302_ = lean_ctor_get(v_c_128_, 0);
lean_inc(v_fvarId_302_);
lean_dec_ref_known(v_c_128_, 1);
lean_inc(v_a_133_);
lean_inc_ref(v_a_132_);
lean_inc(v_a_131_);
lean_inc_ref(v_a_130_);
v___x_303_ = lean_apply_6(v_f_127_, v_fvarId_302_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, lean_box(0));
return v___x_303_;
}
case 6:
{
lean_object* v_type_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_361_; 
v_type_304_ = lean_ctor_get(v_c_128_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_361_ == 0)
{
v___x_306_ = v_c_128_;
v_isShared_307_ = v_isSharedCheck_361_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_type_304_);
lean_dec(v_c_128_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_361_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___x_308_; lean_object* v___x_309_; 
v___x_308_ = 0;
v___x_309_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_126_, v_type_304_, v___x_308_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v_fvarId_311_; lean_object* v___x_312_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_309_, 1);
v_fvarId_311_ = lean_ctor_get(v_a_310_, 0);
lean_inc(v_a_133_);
lean_inc_ref(v_a_132_);
lean_inc(v_a_131_);
lean_inc_ref(v_a_130_);
lean_inc(v_fvarId_311_);
v___x_312_ = lean_apply_6(v_f_127_, v_fvarId_311_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, lean_box(0));
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_314_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc_n(v_a_313_, 2);
lean_dec_ref_known(v___x_312_, 1);
v___x_314_ = l_Lean_Compiler_LCNF_Code_inferType(v_pu_126_, v_a_313_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_316_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
v___x_316_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v_pu_126_, v_a_313_, v_a_131_);
lean_dec(v_a_313_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v___x_317_; 
lean_dec_ref_known(v___x_316_, 1);
v___x_317_ = l_Lean_Compiler_LCNF_eraseParam___redArg(v_pu_126_, v_a_310_, v_a_131_);
lean_dec(v_a_310_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_327_; 
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_327_ == 0)
{
lean_object* v_unused_328_; 
v_unused_328_ = lean_ctor_get(v___x_317_, 0);
lean_dec(v_unused_328_);
v___x_319_ = v___x_317_;
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
else
{
lean_dec(v___x_317_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 0, v_a_315_);
v___x_322_ = v___x_306_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_315_);
v___x_322_ = v_reuseFailAlloc_326_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v___x_322_);
v___x_324_ = v___x_319_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_336_; 
lean_dec(v_a_315_);
lean_del_object(v___x_306_);
v_a_329_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_336_ == 0)
{
v___x_331_ = v___x_317_;
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_317_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_336_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_334_; 
if (v_isShared_332_ == 0)
{
v___x_334_ = v___x_331_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_329_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v_a_315_);
lean_dec(v_a_310_);
lean_del_object(v___x_306_);
v_a_337_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_316_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_316_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_a_313_);
lean_dec(v_a_310_);
lean_del_object(v___x_306_);
v_a_345_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_314_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_314_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_dec(v_a_310_);
lean_del_object(v___x_306_);
return v___x_312_;
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_del_object(v___x_306_);
lean_dec_ref(v_f_127_);
v_a_353_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_309_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_309_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
case 7:
{
lean_object* v_fvarId_362_; lean_object* v_i_363_; lean_object* v_y_364_; lean_object* v_k_365_; lean_object* v___x_366_; 
v_fvarId_362_ = lean_ctor_get(v_c_128_, 0);
v_i_363_ = lean_ctor_get(v_c_128_, 1);
v_y_364_ = lean_ctor_get(v_c_128_, 2);
v_k_365_ = lean_ctor_get(v_c_128_, 3);
lean_inc_ref(v_k_365_);
v___x_366_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_365_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_391_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_391_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_391_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_391_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
size_t v___x_371_; size_t v___x_372_; uint8_t v___x_373_; 
v___x_371_ = lean_ptr_addr(v_k_365_);
v___x_372_ = lean_ptr_addr(v_a_367_);
v___x_373_ = lean_usize_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_383_; 
lean_inc(v_y_364_);
lean_inc(v_i_363_);
lean_inc(v_fvarId_362_);
v_isSharedCheck_383_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; lean_object* v_unused_385_; lean_object* v_unused_386_; lean_object* v_unused_387_; 
v_unused_384_ = lean_ctor_get(v_c_128_, 3);
lean_dec(v_unused_384_);
v_unused_385_ = lean_ctor_get(v_c_128_, 2);
lean_dec(v_unused_385_);
v_unused_386_ = lean_ctor_get(v_c_128_, 1);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_c_128_, 0);
lean_dec(v_unused_387_);
v___x_375_ = v_c_128_;
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
else
{
lean_dec(v_c_128_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 3, v_a_367_);
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(7, 4, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_fvarId_362_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_i_363_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_y_364_);
lean_ctor_set(v_reuseFailAlloc_382_, 3, v_a_367_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_378_);
v___x_380_ = v___x_369_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
else
{
lean_object* v___x_389_; 
lean_dec(v_a_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v_c_128_);
v___x_389_ = v___x_369_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_c_128_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_128_, 4);
return v___x_366_;
}
}
case 8:
{
lean_object* v_fvarId_392_; lean_object* v_i_393_; lean_object* v_y_394_; lean_object* v_k_395_; lean_object* v___x_396_; 
v_fvarId_392_ = lean_ctor_get(v_c_128_, 0);
v_i_393_ = lean_ctor_get(v_c_128_, 1);
v_y_394_ = lean_ctor_get(v_c_128_, 2);
v_k_395_ = lean_ctor_get(v_c_128_, 3);
lean_inc_ref(v_k_395_);
v___x_396_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_395_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_421_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_421_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_421_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_421_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
size_t v___x_401_; size_t v___x_402_; uint8_t v___x_403_; 
v___x_401_ = lean_ptr_addr(v_k_395_);
v___x_402_ = lean_ptr_addr(v_a_397_);
v___x_403_ = lean_usize_dec_eq(v___x_401_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_413_; 
lean_inc(v_y_394_);
lean_inc(v_i_393_);
lean_inc(v_fvarId_392_);
v_isSharedCheck_413_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; lean_object* v_unused_416_; lean_object* v_unused_417_; 
v_unused_414_ = lean_ctor_get(v_c_128_, 3);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v_c_128_, 2);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_c_128_, 1);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_c_128_, 0);
lean_dec(v_unused_417_);
v___x_405_ = v_c_128_;
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
else
{
lean_dec(v_c_128_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_413_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 3, v_a_397_);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_fvarId_392_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_i_393_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_y_394_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_a_397_);
v___x_408_ = v_reuseFailAlloc_412_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_410_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_408_);
v___x_410_ = v___x_399_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v___x_419_; 
lean_dec(v_a_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v_c_128_);
v___x_419_ = v___x_399_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_c_128_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_128_, 4);
return v___x_396_;
}
}
case 9:
{
lean_object* v_fvarId_422_; lean_object* v_i_423_; lean_object* v_offset_424_; lean_object* v_y_425_; lean_object* v_ty_426_; lean_object* v_k_427_; lean_object* v___x_428_; 
v_fvarId_422_ = lean_ctor_get(v_c_128_, 0);
v_i_423_ = lean_ctor_get(v_c_128_, 1);
v_offset_424_ = lean_ctor_get(v_c_128_, 2);
v_y_425_ = lean_ctor_get(v_c_128_, 3);
v_ty_426_ = lean_ctor_get(v_c_128_, 4);
v_k_427_ = lean_ctor_get(v_c_128_, 5);
lean_inc_ref(v_k_427_);
v___x_428_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_427_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_455_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_455_ == 0)
{
v___x_431_ = v___x_428_;
v_isShared_432_ = v_isSharedCheck_455_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_428_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_455_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
size_t v___x_433_; size_t v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_ptr_addr(v_k_427_);
v___x_434_ = lean_ptr_addr(v_a_429_);
v___x_435_ = lean_usize_dec_eq(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_445_; 
lean_inc_ref(v_ty_426_);
lean_inc(v_y_425_);
lean_inc(v_offset_424_);
lean_inc(v_i_423_);
lean_inc(v_fvarId_422_);
v_isSharedCheck_445_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_446_ = lean_ctor_get(v_c_128_, 5);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_c_128_, 4);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_c_128_, 3);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_c_128_, 2);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_c_128_, 1);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_c_128_, 0);
lean_dec(v_unused_451_);
v___x_437_ = v_c_128_;
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_c_128_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 5, v_a_429_);
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fvarId_422_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_i_423_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_offset_424_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_y_425_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_ty_426_);
lean_ctor_set(v_reuseFailAlloc_444_, 5, v_a_429_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_440_);
v___x_442_ = v___x_431_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v___x_453_; 
lean_dec(v_a_429_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v_c_128_);
v___x_453_ = v___x_431_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_c_128_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_128_, 6);
return v___x_428_;
}
}
case 10:
{
lean_object* v_fvarId_456_; lean_object* v_cidx_457_; lean_object* v_k_458_; lean_object* v___x_459_; 
v_fvarId_456_ = lean_ctor_get(v_c_128_, 0);
v_cidx_457_ = lean_ctor_get(v_c_128_, 1);
v_k_458_ = lean_ctor_get(v_c_128_, 2);
lean_inc_ref(v_k_458_);
v___x_459_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_458_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_483_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_483_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_483_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_483_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = lean_ptr_addr(v_k_458_);
v___x_465_ = lean_ptr_addr(v_a_460_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_476_; 
lean_inc(v_cidx_457_);
lean_inc(v_fvarId_456_);
v_isSharedCheck_476_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; lean_object* v_unused_479_; 
v_unused_477_ = lean_ctor_get(v_c_128_, 2);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_c_128_, 1);
lean_dec(v_unused_478_);
v_unused_479_ = lean_ctor_get(v_c_128_, 0);
lean_dec(v_unused_479_);
v___x_468_ = v_c_128_;
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
else
{
lean_dec(v_c_128_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 2, v_a_460_);
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_fvarId_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_cidx_457_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_a_460_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_471_);
v___x_473_ = v___x_462_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v___x_481_; 
lean_dec(v_a_460_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v_c_128_);
v___x_481_ = v___x_462_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_c_128_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_128_, 3);
return v___x_459_;
}
}
case 11:
{
lean_object* v_fvarId_484_; lean_object* v_n_485_; uint8_t v_check_486_; uint8_t v_persistent_487_; lean_object* v_k_488_; lean_object* v___x_489_; 
v_fvarId_484_ = lean_ctor_get(v_c_128_, 0);
v_n_485_ = lean_ctor_get(v_c_128_, 1);
v_check_486_ = lean_ctor_get_uint8(v_c_128_, sizeof(void*)*3);
v_persistent_487_ = lean_ctor_get_uint8(v_c_128_, sizeof(void*)*3 + 1);
v_k_488_ = lean_ctor_get(v_c_128_, 2);
lean_inc_ref(v_k_488_);
v___x_489_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_488_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_513_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_513_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_513_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_513_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
size_t v___x_494_; size_t v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_ptr_addr(v_k_488_);
v___x_495_ = lean_ptr_addr(v_a_490_);
v___x_496_ = lean_usize_dec_eq(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_506_; 
lean_inc(v_n_485_);
lean_inc(v_fvarId_484_);
v_isSharedCheck_506_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; lean_object* v_unused_508_; lean_object* v_unused_509_; 
v_unused_507_ = lean_ctor_get(v_c_128_, 2);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_c_128_, 1);
lean_dec(v_unused_508_);
v_unused_509_ = lean_ctor_get(v_c_128_, 0);
lean_dec(v_unused_509_);
v___x_498_ = v_c_128_;
v_isShared_499_ = v_isSharedCheck_506_;
goto v_resetjp_497_;
}
else
{
lean_dec(v_c_128_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_506_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 2, v_a_490_);
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(11, 3, 2);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_fvarId_484_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_n_485_);
lean_ctor_set(v_reuseFailAlloc_505_, 2, v_a_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*3, v_check_486_);
lean_ctor_set_uint8(v_reuseFailAlloc_505_, sizeof(void*)*3 + 1, v_persistent_487_);
v___x_501_ = v_reuseFailAlloc_505_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_503_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_501_);
v___x_503_ = v___x_492_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec(v_a_490_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v_c_128_);
v___x_511_ = v___x_492_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_c_128_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_128_, 3);
return v___x_489_;
}
}
case 12:
{
lean_object* v_fvarId_514_; lean_object* v_n_515_; uint8_t v_check_516_; uint8_t v_persistent_517_; lean_object* v_objs_x3f_518_; lean_object* v_k_519_; lean_object* v___x_520_; 
v_fvarId_514_ = lean_ctor_get(v_c_128_, 0);
v_n_515_ = lean_ctor_get(v_c_128_, 1);
v_check_516_ = lean_ctor_get_uint8(v_c_128_, sizeof(void*)*4);
v_persistent_517_ = lean_ctor_get_uint8(v_c_128_, sizeof(void*)*4 + 1);
v_objs_x3f_518_ = lean_ctor_get(v_c_128_, 2);
v_k_519_ = lean_ctor_get(v_c_128_, 3);
lean_inc_ref(v_k_519_);
v___x_520_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_519_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_545_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_545_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_545_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_545_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
size_t v___x_525_; size_t v___x_526_; uint8_t v___x_527_; 
v___x_525_ = lean_ptr_addr(v_k_519_);
v___x_526_ = lean_ptr_addr(v_a_521_);
v___x_527_ = lean_usize_dec_eq(v___x_525_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_537_; 
lean_inc(v_objs_x3f_518_);
lean_inc(v_n_515_);
lean_inc(v_fvarId_514_);
v_isSharedCheck_537_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; lean_object* v_unused_539_; lean_object* v_unused_540_; lean_object* v_unused_541_; 
v_unused_538_ = lean_ctor_get(v_c_128_, 3);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_c_128_, 2);
lean_dec(v_unused_539_);
v_unused_540_ = lean_ctor_get(v_c_128_, 1);
lean_dec(v_unused_540_);
v_unused_541_ = lean_ctor_get(v_c_128_, 0);
lean_dec(v_unused_541_);
v___x_529_ = v_c_128_;
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
else
{
lean_dec(v_c_128_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 3, v_a_521_);
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(12, 4, 2);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_fvarId_514_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_n_515_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_objs_x3f_518_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_a_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_536_, sizeof(void*)*4, v_check_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_536_, sizeof(void*)*4 + 1, v_persistent_517_);
v___x_532_ = v_reuseFailAlloc_536_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_532_);
v___x_534_ = v___x_523_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v___x_543_; 
lean_dec(v_a_521_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v_c_128_);
v___x_543_ = v___x_523_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_c_128_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_128_, 4);
return v___x_520_;
}
}
default: 
{
lean_object* v_fvarId_546_; lean_object* v_k_547_; lean_object* v___x_548_; 
v_fvarId_546_ = lean_ctor_get(v_c_128_, 0);
v_k_547_ = lean_ctor_get(v_c_128_, 1);
lean_inc_ref(v_k_547_);
v___x_548_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_k_547_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_571_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_571_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_571_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_571_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
size_t v___x_553_; size_t v___x_554_; uint8_t v___x_555_; 
v___x_553_ = lean_ptr_addr(v_k_547_);
v___x_554_ = lean_ptr_addr(v_a_549_);
v___x_555_ = lean_usize_dec_eq(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_565_; 
lean_inc(v_fvarId_546_);
v_isSharedCheck_565_ = !lean_is_exclusive(v_c_128_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; lean_object* v_unused_567_; 
v_unused_566_ = lean_ctor_get(v_c_128_, 1);
lean_dec(v_unused_566_);
v_unused_567_ = lean_ctor_get(v_c_128_, 0);
lean_dec(v_unused_567_);
v___x_557_ = v_c_128_;
v_isShared_558_ = v_isSharedCheck_565_;
goto v_resetjp_556_;
}
else
{
lean_dec(v_c_128_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_565_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 1, v_a_549_);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(13, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_fvarId_546_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_a_549_);
v___x_560_ = v_reuseFailAlloc_564_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_562_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_560_);
v___x_562_ = v___x_551_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v___x_569_; 
lean_dec(v_a_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v_c_128_);
v___x_569_ = v___x_551_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_c_128_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
lean_dec_ref_known(v_c_128_, 2);
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_126_ = stack[0].m_num;
lean_object* v_f_127_ = stack[1].m_obj;
lean_object* v_c_128_ = stack[2].m_obj;
lean_object* v_a_129_ = stack[3].m_obj;
lean_object* v_a_130_ = stack[4].m_obj;
lean_object* v_a_131_ = stack[5].m_obj;
lean_object* v_a_132_ = stack[6].m_obj;
lean_object* v_a_133_ = stack[7].m_obj;
lean_object* v_res_572_;
v_res_572_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_126_, v_f_127_, v_c_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
stack->m_obj
 = v_res_572_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(uint8_t v_pu_573_, lean_object* v_f_574_, size_t v_sz_575_, size_t v_i_576_, lean_object* v_bs_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = lean_usize_dec_lt(v_i_576_, v_sz_575_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_dec_ref(v_f_574_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v_bs_577_);
return v___x_585_;
}
else
{
lean_object* v_v_586_; lean_object* v___x_587_; lean_object* v_bs_x27_588_; lean_object* v_a_590_; 
v_v_586_ = lean_array_uget(v_bs_577_, v_i_576_);
v___x_587_ = lean_unsigned_to_nat(0u);
v_bs_x27_588_ = lean_array_uset(v_bs_577_, v_i_576_, v___x_587_);
switch(lean_obj_tag(v_v_586_))
{
case 0:
{
lean_object* v_ctorName_595_; lean_object* v_params_596_; lean_object* v_code_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_614_; 
v_ctorName_595_ = lean_ctor_get(v_v_586_, 0);
v_params_596_ = lean_ctor_get(v_v_586_, 1);
v_code_597_ = lean_ctor_get(v_v_586_, 2);
v_isSharedCheck_614_ = !lean_is_exclusive(v_v_586_);
if (v_isSharedCheck_614_ == 0)
{
v___x_599_ = v_v_586_;
v_isShared_600_ = v_isSharedCheck_614_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_code_597_);
lean_inc(v_params_596_);
lean_inc(v_ctorName_595_);
lean_dec(v_v_586_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_614_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; 
lean_inc_ref(v_f_574_);
v___x_601_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_573_, v_f_574_, v_code_597_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 2, v_a_602_);
v___x_604_ = v___x_599_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_ctorName_595_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_params_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_a_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
v_a_590_ = v___x_604_;
goto v___jp_589_;
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_del_object(v___x_599_);
lean_dec_ref(v_params_596_);
lean_dec(v_ctorName_595_);
lean_dec_ref(v_bs_x27_588_);
lean_dec_ref(v_f_574_);
v_a_606_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_601_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_601_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
case 1:
{
lean_object* v_info_615_; lean_object* v_code_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_633_; 
v_info_615_ = lean_ctor_get(v_v_586_, 0);
v_code_616_ = lean_ctor_get(v_v_586_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_v_586_);
if (v_isSharedCheck_633_ == 0)
{
v___x_618_ = v_v_586_;
v_isShared_619_ = v_isSharedCheck_633_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_code_616_);
lean_inc(v_info_615_);
lean_dec(v_v_586_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_633_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; 
lean_inc_ref(v_f_574_);
v___x_620_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_573_, v_f_574_, v_code_616_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v_a_621_);
v___x_623_ = v___x_618_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_info_615_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_a_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
v_a_590_ = v___x_623_;
goto v___jp_589_;
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_del_object(v___x_618_);
lean_dec_ref(v_info_615_);
lean_dec_ref(v_bs_x27_588_);
lean_dec_ref(v_f_574_);
v_a_625_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_620_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_620_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
default: 
{
lean_object* v_code_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_651_; 
v_code_634_ = lean_ctor_get(v_v_586_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_v_586_);
if (v_isSharedCheck_651_ == 0)
{
v___x_636_ = v_v_586_;
v_isShared_637_ = v_isSharedCheck_651_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_code_634_);
lean_dec(v_v_586_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_651_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; 
lean_inc_ref(v_f_574_);
v___x_638_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_573_, v_f_574_, v_code_634_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_a_639_);
v___x_641_ = v___x_636_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
v_a_590_ = v___x_641_;
goto v___jp_589_;
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_del_object(v___x_636_);
lean_dec_ref(v_bs_x27_588_);
lean_dec_ref(v_f_574_);
v_a_643_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_638_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_638_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
v___jp_589_:
{
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_591_ = ((size_t)1ULL);
v___x_592_ = lean_usize_add(v_i_576_, v___x_591_);
v___x_593_ = lean_array_uset(v_bs_x27_588_, v_i_576_, v_a_590_);
v_i_576_ = v___x_592_;
v_bs_577_ = v___x_593_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_573_ = stack[0].m_num;
lean_object* v_f_574_ = stack[1].m_obj;
size_t v_sz_575_ = stack[2].m_num;
size_t v_i_576_ = stack[3].m_num;
lean_object* v_bs_577_ = stack[4].m_obj;
lean_object* v___y_578_ = stack[5].m_obj;
lean_object* v___y_579_ = stack[6].m_obj;
lean_object* v___y_580_ = stack[7].m_obj;
lean_object* v___y_581_ = stack[8].m_obj;
lean_object* v___y_582_ = stack[9].m_obj;
lean_object* v_res_652_;
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(v_pu_573_, v_f_574_, v_sz_575_, v_i_576_, v_bs_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
stack->m_obj
 = v_res_652_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2___boxed(lean_object* v_pu_653_, lean_object* v_f_654_, lean_object* v_sz_655_, lean_object* v_i_656_, lean_object* v_bs_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
uint8_t v_pu_boxed_664_; size_t v_sz_boxed_665_; size_t v_i_boxed_666_; lean_object* v_res_667_; 
v_pu_boxed_664_ = lean_unbox(v_pu_653_);
v_sz_boxed_665_ = lean_unbox_usize(v_sz_655_);
lean_dec(v_sz_655_);
v_i_boxed_666_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_res_667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__2(v_pu_boxed_664_, v_f_654_, v_sz_boxed_665_, v_i_boxed_666_, v_bs_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go___boxed(lean_object* v_pu_668_, lean_object* v_f_669_, lean_object* v_c_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
uint8_t v_pu_boxed_677_; lean_object* v_res_678_; 
v_pu_boxed_677_ = lean_unbox(v_pu_668_);
v_res_678_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_boxed_677_, v_f_669_, v_c_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
return v_res_678_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(lean_object* v_00_u03b2_679_, lean_object* v_k_680_, lean_object* v_t_681_){
_start:
{
uint8_t v___x_682_; 
v___x_682_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___redArg(v_k_680_, v_t_681_);
return v___x_682_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_680_ = stack[1].m_obj;
lean_object* v_t_681_ = stack[2].m_obj;
uint8_t v_res_683_;
v_res_683_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(lean_box(0), v_k_680_, v_t_681_);
stack->m_num = v_res_683_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0___boxed(lean_object* v_00_u03b2_684_, lean_object* v_k_685_, lean_object* v_t_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go_spec__0(v_00_u03b2_684_, v_k_685_, v_t_686_);
lean_dec(v_t_686_);
lean_dec(v_k_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(uint8_t v_pu_689_, lean_object* v_c_690_, lean_object* v_f_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(1);
v___x_698_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_CompilerM_codeBind_go(v_pu_689_, v_f_691_, v_c_690_, v___x_697_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
return v___x_698_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CompilerM_codeBind_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_689_ = stack[0].m_num;
lean_object* v_c_690_ = stack[1].m_obj;
lean_object* v_f_691_ = stack[2].m_obj;
lean_object* v_a_692_ = stack[3].m_obj;
lean_object* v_a_693_ = stack[4].m_obj;
lean_object* v_a_694_ = stack[5].m_obj;
lean_object* v_a_695_ = stack[6].m_obj;
lean_object* v_res_699_;
v_res_699_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v_pu_689_, v_c_690_, v_f_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
stack->m_obj
 = v_res_699_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind___boxed(lean_object* v_pu_700_, lean_object* v_c_701_, lean_object* v_f_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
uint8_t v_pu_boxed_708_; lean_object* v_res_709_; 
v_pu_boxed_708_ = lean_unbox(v_pu_700_);
v_res_709_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v_pu_boxed_708_, v_c_701_, v_f_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0(lean_object* v_f_712_, lean_object* v_ctx_713_, lean_object* v_fvarId_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_apply_2(v_f_712_, v_fvarId_714_, v_ctx_713_);
return v___x_715_;
}
}
lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(lean_object* v_inst_716_, uint8_t v_pu_717_, lean_object* v_c_718_, lean_object* v_f_719_, lean_object* v_ctx_720_){
_start:
{
lean_object* v___f_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___f_721_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_721_, 0, v_f_719_);
lean_closure_set(v___f_721_, 1, v_ctx_720_);
v___x_722_ = lean_box(v_pu_717_);
v___x_723_ = lean_apply_3(v_inst_716_, v___x_722_, v_c_718_, v___f_721_);
return v___x_723_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_716_ = stack[0].m_obj;
uint8_t v_pu_717_ = stack[1].m_num;
lean_object* v_c_718_ = stack[2].m_obj;
lean_object* v_f_719_ = stack[3].m_obj;
lean_object* v_ctx_720_ = stack[4].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(v_inst_716_, v_pu_717_, v_c_718_, v_f_719_, v_ctx_720_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed(lean_object* v_inst_725_, lean_object* v_pu_726_, lean_object* v_c_727_, lean_object* v_f_728_, lean_object* v_ctx_729_){
_start:
{
uint8_t v_pu_22__boxed_730_; lean_object* v_res_731_; 
v_pu_22__boxed_730_ = lean_unbox(v_pu_726_);
v_res_731_ = l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1(v_inst_725_, v_pu_22__boxed_730_, v_c_727_, v_f_728_, v_ctx_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg(lean_object* v_inst_732_){
_start:
{
lean_object* v___f_733_; 
v___f_733_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_733_, 0, v_inst_732_);
return v___f_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindReaderT(lean_object* v_m_734_, lean_object* v_00_u03c1_735_, lean_object* v_inst_736_){
_start:
{
lean_object* v___f_737_; 
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindReaderT___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_737_, 0, v_inst_736_);
return v___f_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0(lean_object* v_f_738_, lean_object* v_sref_739_, lean_object* v_fvarId_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_apply_2(v_f_738_, v_fvarId_740_, v_sref_739_);
return v___x_741_;
}
}
lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(lean_object* v_inst_742_, uint8_t v_pu_743_, lean_object* v_c_744_, lean_object* v_f_745_, lean_object* v_sref_746_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___f_747_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__0), 3, 2);
lean_closure_set(v___f_747_, 0, v_f_745_);
lean_closure_set(v___f_747_, 1, v_sref_746_);
v___x_748_ = lean_box(v_pu_743_);
v___x_749_ = lean_apply_3(v_inst_742_, v___x_748_, v_c_744_, v___f_747_);
return v___x_749_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_742_ = stack[0].m_obj;
uint8_t v_pu_743_ = stack[1].m_num;
lean_object* v_c_744_ = stack[2].m_obj;
lean_object* v_f_745_ = stack[3].m_obj;
lean_object* v_sref_746_ = stack[4].m_obj;
lean_object* v_res_750_;
v_res_750_ = l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(v_inst_742_, v_pu_743_, v_c_744_, v_f_745_, v_sref_746_);
stack->m_obj
 = v_res_750_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed(lean_object* v_inst_751_, lean_object* v_pu_752_, lean_object* v_c_753_, lean_object* v_f_754_, lean_object* v_sref_755_){
_start:
{
uint8_t v_pu_24__boxed_756_; lean_object* v_res_757_; 
v_pu_24__boxed_756_ = lean_unbox(v_pu_752_);
v_res_757_ = l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1(v_inst_751_, v_pu_24__boxed_756_, v_c_753_, v_f_754_, v_sref_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg(lean_object* v_inst_758_){
_start:
{
lean_object* v___f_759_; 
v___f_759_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_759_, 0, v_inst_758_);
return v___f_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld(lean_object* v_00_u03c9_760_, lean_object* v_m_761_, lean_object* v_00_u03c3_762_, lean_object* v_inst_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v___f_765_; 
v___f_765_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCodeBindStateRefT_x27OfSTWorld___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_765_, 0, v_inst_764_);
return v___f_765_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(uint8_t v_pu_768_, lean_object* v_type_769_, lean_object* v_xs_770_, lean_object* v_ps_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
if (lean_obj_tag(v_type_769_) == 7)
{
lean_object* v_binderType_777_; lean_object* v_body_778_; lean_object* v_d_779_; uint8_t v___x_780_; lean_object* v___x_781_; 
v_binderType_777_ = lean_ctor_get(v_type_769_, 1);
lean_inc_ref(v_binderType_777_);
v_body_778_ = lean_ctor_get(v_type_769_, 2);
lean_inc_ref(v_body_778_);
lean_dec_ref_known(v_type_769_, 3);
v_d_779_ = lean_expr_instantiate_rev(v_binderType_777_, v_xs_770_);
lean_dec_ref(v_binderType_777_);
v___x_780_ = l_Lean_isMarkedBorrowed(v_d_779_);
v___x_781_ = l_Lean_Compiler_LCNF_mkAuxParam(v_pu_768_, v_d_779_, v___x_780_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v_fvarId_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v_fvarId_783_ = lean_ctor_get(v_a_782_, 0);
lean_inc(v_fvarId_783_);
v___x_784_ = l_Lean_Expr_fvar___override(v_fvarId_783_);
v___x_785_ = lean_array_push(v_xs_770_, v___x_784_);
v___x_786_ = lean_array_push(v_ps_771_, v_a_782_);
v_type_769_ = v_body_778_;
v_xs_770_ = v___x_785_;
v_ps_771_ = v___x_786_;
goto _start;
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec_ref(v_body_778_);
lean_dec_ref(v_ps_771_);
lean_dec_ref(v_xs_770_);
v_a_788_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_781_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_781_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_type_796_; lean_object* v_type_x27_797_; uint8_t v___x_798_; 
v_type_796_ = lean_expr_instantiate_rev(v_type_769_, v_xs_770_);
lean_dec_ref(v_xs_770_);
lean_dec_ref(v_type_769_);
lean_inc_ref(v_type_796_);
v_type_x27_797_ = l_Lean_Expr_headBeta(v_type_796_);
v___x_798_ = lean_expr_eqv(v_type_x27_797_, v_type_796_);
lean_dec_ref(v_type_796_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
v___x_799_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0));
v_type_769_ = v_type_x27_797_;
v_xs_770_ = v___x_799_;
goto _start;
}
else
{
lean_object* v___x_801_; 
lean_dec_ref(v_type_x27_797_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_ps_771_);
return v___x_801_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_768_ = stack[0].m_num;
lean_object* v_type_769_ = stack[1].m_obj;
lean_object* v_xs_770_ = stack[2].m_obj;
lean_object* v_ps_771_ = stack[3].m_obj;
lean_object* v_a_772_ = stack[4].m_obj;
lean_object* v_a_773_ = stack[5].m_obj;
lean_object* v_a_774_ = stack[6].m_obj;
lean_object* v_a_775_ = stack[7].m_obj;
lean_object* v_res_802_;
v_res_802_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(v_pu_768_, v_type_769_, v_xs_770_, v_ps_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
stack->m_obj
 = v_res_802_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___boxed(lean_object* v_pu_803_, lean_object* v_type_804_, lean_object* v_xs_805_, lean_object* v_ps_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
uint8_t v_pu_boxed_812_; lean_object* v_res_813_; 
v_pu_boxed_812_ = lean_unbox(v_pu_803_);
v_res_813_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(v_pu_boxed_812_, v_type_804_, v_xs_805_, v_ps_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_813_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkNewParams(uint8_t v_pu_814_, lean_object* v_type_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go___closed__0));
v___x_822_ = l___private_Lean_Compiler_LCNF_Bind_0__Lean_Compiler_LCNF_mkNewParams_go(v_pu_814_, v_type_815_, v___x_821_, v___x_821_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
return v___x_822_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkNewParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_814_ = stack[0].m_num;
lean_object* v_type_815_ = stack[1].m_obj;
lean_object* v_a_816_ = stack[2].m_obj;
lean_object* v_a_817_ = stack[3].m_obj;
lean_object* v_a_818_ = stack[4].m_obj;
lean_object* v_a_819_ = stack[5].m_obj;
lean_object* v_res_823_;
v_res_823_ = l_Lean_Compiler_LCNF_mkNewParams(v_pu_814_, v_type_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkNewParams___boxed(lean_object* v_pu_824_, lean_object* v_type_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
uint8_t v_pu_boxed_831_; lean_object* v_res_832_; 
v_pu_boxed_831_ = lean_unbox(v_pu_824_);
v_res_832_ = l_Lean_Compiler_LCNF_mkNewParams(v_pu_boxed_831_, v_type_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_832_;
}
}
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object* v_type_833_, lean_object* v_params_834_){
_start:
{
lean_object* v_typeArity_835_; lean_object* v_valueArity_836_; uint8_t v___x_837_; 
v_typeArity_835_ = l_Lean_Compiler_LCNF_getArrowArity(v_type_833_);
v_valueArity_836_ = lean_array_get_size(v_params_834_);
v___x_837_ = lean_nat_dec_lt(v_valueArity_836_, v_typeArity_835_);
lean_dec(v_typeArity_835_);
return v___x_837_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isEtaExpandCandidateCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_833_ = stack[0].m_obj;
lean_object* v_params_834_ = stack[1].m_obj;
uint8_t v_res_838_;
v_res_838_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_833_, v_params_834_);
stack->m_num = v_res_838_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isEtaExpandCandidateCore___boxed(lean_object* v_type_839_, lean_object* v_params_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_839_, v_params_840_);
lean_dec_ref(v_params_840_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
uint8_t l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(lean_object* v_decl_843_){
_start:
{
lean_object* v_params_844_; lean_object* v_type_845_; uint8_t v___x_846_; 
v_params_844_ = lean_ctor_get(v_decl_843_, 2);
lean_inc_ref(v_params_844_);
v_type_845_ = lean_ctor_get(v_decl_843_, 3);
lean_inc_ref(v_type_845_);
lean_dec_ref(v_decl_843_);
v___x_846_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_845_, v_params_844_);
lean_dec_ref(v_params_844_);
return v___x_846_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_843_ = stack[0].m_obj;
uint8_t v_res_847_;
v_res_847_ = l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(v_decl_843_);
stack->m_num = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate___boxed(lean_object* v_decl_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Lean_Compiler_LCNF_FunDecl_isEtaExpandCandidate(v_decl_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0(lean_object* v___x_854_, uint8_t v___x_855_, lean_object* v_fvarId_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_862_, 0, v_fvarId_856_);
lean_ctor_set(v___x_862_, 1, v___x_854_);
v___x_863_ = ((lean_object*)(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___closed__1));
v___x_864_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_855_, v___x_862_, v___x_863_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_875_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_875_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_875_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_fvarId_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v_fvarId_869_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_fvarId_869_);
v___x_870_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_870_, 0, v_fvarId_869_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v_a_865_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_871_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_a_876_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_864_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_864_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_etaExpandCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_854_ = stack[0].m_obj;
uint8_t v___x_855_ = stack[1].m_num;
lean_object* v_fvarId_856_ = stack[2].m_obj;
lean_object* v___y_857_ = stack[3].m_obj;
lean_object* v___y_858_ = stack[4].m_obj;
lean_object* v___y_859_ = stack[5].m_obj;
lean_object* v___y_860_ = stack[6].m_obj;
lean_object* v_res_884_;
v_res_884_ = l_Lean_Compiler_LCNF_etaExpandCore___lam__0(v___x_854_, v___x_855_, v_fvarId_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
stack->m_obj
 = v_res_884_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed(lean_object* v___x_885_, lean_object* v___x_886_, lean_object* v_fvarId_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
uint8_t v___x_900__boxed_893_; lean_object* v_res_894_; 
v___x_900__boxed_893_ = lean_unbox(v___x_886_);
v_res_894_ = l_Lean_Compiler_LCNF_etaExpandCore___lam__0(v___x_885_, v___x_900__boxed_893_, v_fvarId_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
return v_res_894_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(size_t v_sz_895_, size_t v_i_896_, lean_object* v_bs_897_){
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
v___x_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_903_, 0, v_fvarId_900_);
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_add(v_i_896_, v___x_904_);
v___x_906_ = lean_array_uset(v_bs_x27_902_, v_i_896_, v___x_903_);
v_i_896_ = v___x_905_;
v_bs_897_ = v___x_906_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_895_ = stack[0].m_num;
size_t v_i_896_ = stack[1].m_num;
lean_object* v_bs_897_ = stack[2].m_obj;
lean_object* v_res_908_;
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_895_, v_i_896_, v_bs_897_);
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1___boxed(lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_bs_911_){
_start:
{
size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_sz_boxed_912_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_913_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_boxed_912_, v_i_boxed_913_, v_bs_911_);
return v_res_914_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(size_t v_sz_915_, size_t v_i_916_, lean_object* v_bs_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = lean_usize_dec_lt(v_i_916_, v_sz_915_);
if (v___x_918_ == 0)
{
return v_bs_917_;
}
else
{
lean_object* v_v_919_; lean_object* v_fvarId_920_; lean_object* v___x_921_; lean_object* v_bs_x27_922_; lean_object* v___x_923_; size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; 
v_v_919_ = lean_array_uget_borrowed(v_bs_917_, v_i_916_);
v_fvarId_920_ = lean_ctor_get(v_v_919_, 0);
lean_inc(v_fvarId_920_);
v___x_921_ = lean_unsigned_to_nat(0u);
v_bs_x27_922_ = lean_array_uset(v_bs_917_, v_i_916_, v___x_921_);
v___x_923_ = l_Lean_mkFVar(v_fvarId_920_);
v___x_924_ = ((size_t)1ULL);
v___x_925_ = lean_usize_add(v_i_916_, v___x_924_);
v___x_926_ = lean_array_uset(v_bs_x27_922_, v_i_916_, v___x_923_);
v_i_916_ = v___x_925_;
v_bs_917_ = v___x_926_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_915_ = stack[0].m_num;
size_t v_i_916_ = stack[1].m_num;
lean_object* v_bs_917_ = stack[2].m_obj;
lean_object* v_res_928_;
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_915_, v_i_916_, v_bs_917_);
stack->m_obj
 = v_res_928_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0___boxed(lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_bs_931_){
_start:
{
size_t v_sz_boxed_932_; size_t v_i_boxed_933_; lean_object* v_res_934_; 
v_sz_boxed_932_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_933_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_boxed_932_, v_i_boxed_933_, v_bs_931_);
return v_res_934_;
}
}
lean_object* l_Lean_Compiler_LCNF_etaExpandCore(lean_object* v_type_935_, lean_object* v_params_936_, lean_object* v_value_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
size_t v_sz_943_; size_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_sz_943_ = lean_array_size(v_params_936_);
v___x_944_ = ((size_t)0ULL);
lean_inc_ref(v_params_936_);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__0(v_sz_943_, v___x_944_, v_params_936_);
v___x_946_ = l_Lean_Compiler_LCNF_instantiateForall(v_type_935_, v___x_945_, v_a_940_, v_a_941_);
lean_dec_ref(v___x_945_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___x_948_; lean_object* v___x_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = 0;
v___x_949_ = l_Lean_Compiler_LCNF_mkNewParams(v___x_948_, v_a_947_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_951_; size_t v_sz_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___f_955_; lean_object* v___x_956_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v___x_951_ = l_Array_append___redArg(v_params_936_, v_a_950_);
v_sz_952_ = lean_array_size(v_a_950_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_etaExpandCore_spec__1(v_sz_952_, v___x_944_, v_a_950_);
v___x_954_ = lean_box(v___x_948_);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_etaExpandCore___lam__0___boxed), 8, 2);
lean_closure_set(v___f_955_, 0, v___x_953_);
lean_closure_set(v___f_955_, 1, v___x_954_);
v___x_956_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(v___x_948_, v_value_937_, v___f_955_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_965_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_951_);
lean_ctor_set(v___x_961_, 1, v_a_957_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec_ref(v___x_951_);
v_a_966_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_956_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_956_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v_value_937_);
lean_dec_ref(v_params_936_);
v_a_974_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_949_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_949_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec_ref(v_value_937_);
lean_dec_ref(v_params_936_);
v_a_982_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_946_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_946_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_etaExpandCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_935_ = stack[0].m_obj;
lean_object* v_params_936_ = stack[1].m_obj;
lean_object* v_value_937_ = stack[2].m_obj;
lean_object* v_a_938_ = stack[3].m_obj;
lean_object* v_a_939_ = stack[4].m_obj;
lean_object* v_a_940_ = stack[5].m_obj;
lean_object* v_a_941_ = stack[6].m_obj;
lean_object* v_res_990_;
v_res_990_ = l_Lean_Compiler_LCNF_etaExpandCore(v_type_935_, v_params_936_, v_value_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
stack->m_obj
 = v_res_990_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore___boxed(lean_object* v_type_991_, lean_object* v_params_992_, lean_object* v_value_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Compiler_LCNF_etaExpandCore(v_type_991_, v_params_992_, v_value_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_999_;
}
}
lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f(lean_object* v_type_1000_, lean_object* v_params_1001_, lean_object* v_value_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
uint8_t v___x_1008_; 
lean_inc_ref(v_type_1000_);
v___x_1008_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(v_type_1000_, v_params_1001_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
lean_dec_ref(v_value_1002_);
lean_dec_ref(v_params_1001_);
lean_dec_ref(v_type_1000_);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
else
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Compiler_LCNF_etaExpandCore(v_type_1000_, v_params_1001_, v_value_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_a_1012_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
v_a_1021_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1011_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1011_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_etaExpandCore_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1000_ = stack[0].m_obj;
lean_object* v_params_1001_ = stack[1].m_obj;
lean_object* v_value_1002_ = stack[2].m_obj;
lean_object* v_a_1003_ = stack[3].m_obj;
lean_object* v_a_1004_ = stack[4].m_obj;
lean_object* v_a_1005_ = stack[5].m_obj;
lean_object* v_a_1006_ = stack[6].m_obj;
lean_object* v_res_1029_;
v_res_1029_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1000_, v_params_1001_, v_value_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_);
stack->m_obj
 = v_res_1029_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_etaExpandCore_x3f___boxed(lean_object* v_type_1030_, lean_object* v_params_1031_, lean_object* v_value_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1030_, v_params_1031_, v_value_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1038_;
}
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object* v_decl_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_params_1045_; lean_object* v_type_1046_; lean_object* v_value_1047_; uint8_t v___x_1048_; lean_object* v___x_1049_; 
v_params_1045_ = lean_ctor_get(v_decl_1039_, 2);
v_type_1046_ = lean_ctor_get(v_decl_1039_, 3);
v_value_1047_ = lean_ctor_get(v_decl_1039_, 4);
v___x_1048_ = 0;
lean_inc_ref(v_value_1047_);
lean_inc_ref(v_params_1045_);
lean_inc_ref(v_type_1046_);
v___x_1049_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1046_, v_params_1045_, v_value_1047_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1061_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1061_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
if (lean_obj_tag(v_a_1050_) == 1)
{
lean_object* v_val_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; lean_object* v___x_1057_; 
lean_inc_ref(v_type_1046_);
lean_del_object(v___x_1052_);
v_val_1054_ = lean_ctor_get(v_a_1050_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v_a_1050_, 1);
v_fst_1055_ = lean_ctor_get(v_val_1054_, 0);
lean_inc(v_fst_1055_);
v_snd_1056_ = lean_ctor_get(v_val_1054_, 1);
lean_inc(v_snd_1056_);
lean_dec(v_val_1054_);
v___x_1057_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1048_, v_decl_1039_, v_type_1046_, v_fst_1055_, v_snd_1056_, v_a_1041_);
return v___x_1057_;
}
else
{
lean_object* v___x_1059_; 
lean_dec(v_a_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_decl_1039_);
v___x_1059_ = v___x_1052_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_decl_1039_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_decl_1039_);
v_a_1062_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1049_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1049_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_etaExpand_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1039_ = stack[0].m_obj;
lean_object* v_a_1040_ = stack[1].m_obj;
lean_object* v_a_1041_ = stack[2].m_obj;
lean_object* v_a_1042_ = stack[3].m_obj;
lean_object* v_a_1043_ = stack[4].m_obj;
lean_object* v_res_1070_;
v_res_1070_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_decl_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
stack->m_obj
 = v_res_1070_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand___boxed(lean_object* v_decl_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(v_decl_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
return v_res_1077_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object* v_decl_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_value_1084_; 
v_value_1084_ = lean_ctor_get(v_decl_1078_, 1);
lean_inc_ref(v_value_1084_);
if (lean_obj_tag(v_value_1084_) == 0)
{
lean_object* v_toSignature_1085_; uint8_t v_recursive_1086_; lean_object* v_inlineAttr_x3f_1087_; lean_object* v_code_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1140_; 
v_toSignature_1085_ = lean_ctor_get(v_decl_1078_, 0);
lean_inc_ref(v_toSignature_1085_);
v_recursive_1086_ = lean_ctor_get_uint8(v_decl_1078_, sizeof(void*)*3);
v_inlineAttr_x3f_1087_ = lean_ctor_get(v_decl_1078_, 2);
v_code_1088_ = lean_ctor_get(v_value_1084_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_value_1084_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1090_ = v_value_1084_;
v_isShared_1091_ = v_isSharedCheck_1140_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_code_1088_);
lean_dec(v_value_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1140_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_name_1092_; lean_object* v_levelParams_1093_; lean_object* v_type_1094_; lean_object* v_params_1095_; uint8_t v_safe_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1139_; 
v_name_1092_ = lean_ctor_get(v_toSignature_1085_, 0);
v_levelParams_1093_ = lean_ctor_get(v_toSignature_1085_, 1);
v_type_1094_ = lean_ctor_get(v_toSignature_1085_, 2);
v_params_1095_ = lean_ctor_get(v_toSignature_1085_, 3);
v_safe_1096_ = lean_ctor_get_uint8(v_toSignature_1085_, sizeof(void*)*4);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_toSignature_1085_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1098_ = v_toSignature_1085_;
v_isShared_1099_ = v_isSharedCheck_1139_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_params_1095_);
lean_inc(v_type_1094_);
lean_inc(v_levelParams_1093_);
lean_inc(v_name_1092_);
lean_dec(v_toSignature_1085_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1139_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; 
lean_inc_ref(v_type_1094_);
v___x_1100_ = l_Lean_Compiler_LCNF_etaExpandCore_x3f(v_type_1094_, v_params_1095_, v_code_1088_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1130_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1103_ = v___x_1100_;
v_isShared_1104_ = v_isSharedCheck_1130_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1100_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1130_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
if (lean_obj_tag(v_a_1101_) == 1)
{
lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1123_; 
lean_inc(v_inlineAttr_x3f_1087_);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_decl_1078_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; lean_object* v_unused_1125_; lean_object* v_unused_1126_; 
v_unused_1124_ = lean_ctor_get(v_decl_1078_, 2);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_decl_1078_, 1);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v_decl_1078_, 0);
lean_dec(v_unused_1126_);
v___x_1106_ = v_decl_1078_;
v_isShared_1107_ = v_isSharedCheck_1123_;
goto v_resetjp_1105_;
}
else
{
lean_dec(v_decl_1078_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1123_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v_val_1108_; lean_object* v_fst_1109_; lean_object* v_snd_1110_; lean_object* v___x_1112_; 
v_val_1108_ = lean_ctor_get(v_a_1101_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v_a_1101_, 1);
v_fst_1109_ = lean_ctor_get(v_val_1108_, 0);
lean_inc(v_fst_1109_);
v_snd_1110_ = lean_ctor_get(v_val_1108_, 1);
lean_inc(v_snd_1110_);
lean_dec(v_val_1108_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 3, v_fst_1109_);
v___x_1112_ = v___x_1098_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_name_1092_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_levelParams_1093_);
lean_ctor_set(v_reuseFailAlloc_1122_, 2, v_type_1094_);
lean_ctor_set(v_reuseFailAlloc_1122_, 3, v_fst_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1122_, sizeof(void*)*4, v_safe_1096_);
v___x_1112_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_snd_1110_);
v___x_1114_ = v___x_1090_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_snd_1110_);
v___x_1114_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___x_1114_);
lean_ctor_set(v___x_1106_, 0, v___x_1112_);
v___x_1116_ = v___x_1106_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_inlineAttr_x3f_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1120_, sizeof(void*)*3, v_recursive_1086_);
v___x_1116_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
lean_object* v___x_1118_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v___x_1116_);
v___x_1118_ = v___x_1103_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
else
{
lean_object* v___x_1128_; 
lean_dec(v_a_1101_);
lean_del_object(v___x_1098_);
lean_dec_ref(v_type_1094_);
lean_dec(v_levelParams_1093_);
lean_dec(v_name_1092_);
lean_del_object(v___x_1090_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v_decl_1078_);
v___x_1128_ = v___x_1103_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_decl_1078_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_del_object(v___x_1098_);
lean_dec_ref(v_type_1094_);
lean_dec(v_levelParams_1093_);
lean_dec(v_name_1092_);
lean_del_object(v___x_1090_);
lean_dec_ref(v_decl_1078_);
v_a_1131_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1100_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1100_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref_known(v_value_1084_, 1);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v_decl_1078_);
return v___x_1141_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_etaExpand_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1078_ = stack[0].m_obj;
lean_object* v_a_1079_ = stack[1].m_obj;
lean_object* v_a_1080_ = stack[2].m_obj;
lean_object* v_a_1081_ = stack[3].m_obj;
lean_object* v_a_1082_ = stack[4].m_obj;
lean_object* v_res_1142_;
v_res_1142_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
stack->m_obj
 = v_res_1142_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand___boxed(lean_object* v_decl_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
return v_res_1149_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
