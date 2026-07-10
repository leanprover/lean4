// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.InlineProj
// Imports: public import Lean.Compiler.LCNF.Simp.SimpM
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
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instInhabitedOfPure___redArg(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isClass_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instMonadSimpM___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "_private.Lean.Compiler.LCNF.Simp.InlineProj.0.Lean.Compiler.LCNF.Simp.inlineProjInst\?.visit"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Compiler.LCNF.Simp.InlineProj"};
static const lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(lean_object* v_msg_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_toApplicative_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_114_; 
v___x_18_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__0);
v___x_19_ = l_StateRefT_x27_instMonad___redArg(v___x_18_);
v_toApplicative_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; 
v_unused_115_ = lean_ctor_get(v___x_19_, 1);
lean_dec(v_unused_115_);
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_114_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_toApplicative_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_114_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v_toFunctor_24_; lean_object* v_toSeq_25_; lean_object* v_toSeqLeft_26_; lean_object* v_toSeqRight_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_112_; 
v_toFunctor_24_ = lean_ctor_get(v_toApplicative_20_, 0);
v_toSeq_25_ = lean_ctor_get(v_toApplicative_20_, 2);
v_toSeqLeft_26_ = lean_ctor_get(v_toApplicative_20_, 3);
v_toSeqRight_27_ = lean_ctor_get(v_toApplicative_20_, 4);
v_isSharedCheck_112_ = !lean_is_exclusive(v_toApplicative_20_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; 
v_unused_113_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_dec(v_unused_113_);
v___x_29_ = v_toApplicative_20_;
v_isShared_30_ = v_isSharedCheck_112_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_toSeqRight_27_);
lean_inc(v_toSeqLeft_26_);
lean_inc(v_toSeq_25_);
lean_inc(v_toFunctor_24_);
lean_dec(v_toApplicative_20_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_112_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_40_; 
v___f_31_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__1));
v___f_32_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__2));
lean_inc_ref(v_toFunctor_24_);
v___f_33_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_33_, 0, v_toFunctor_24_);
v___f_34_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_34_, 0, v_toFunctor_24_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___f_33_);
lean_ctor_set(v___x_35_, 1, v___f_34_);
v___f_36_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_36_, 0, v_toSeqRight_27_);
v___f_37_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_37_, 0, v_toSeqLeft_26_);
v___f_38_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_38_, 0, v_toSeq_25_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 4, v___f_36_);
lean_ctor_set(v___x_29_, 3, v___f_37_);
lean_ctor_set(v___x_29_, 2, v___f_38_);
lean_ctor_set(v___x_29_, 1, v___f_31_);
lean_ctor_set(v___x_29_, 0, v___x_35_);
v___x_40_ = v___x_29_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___f_31_);
lean_ctor_set(v_reuseFailAlloc_111_, 2, v___f_38_);
lean_ctor_set(v_reuseFailAlloc_111_, 3, v___f_37_);
lean_ctor_set(v_reuseFailAlloc_111_, 4, v___f_36_);
v___x_40_ = v_reuseFailAlloc_111_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___f_32_);
lean_ctor_set(v___x_22_, 0, v___x_40_);
v___x_42_ = v___x_22_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___f_32_);
v___x_42_ = v_reuseFailAlloc_110_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v_toApplicative_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_108_; 
v___x_43_ = l_StateRefT_x27_instMonad___redArg(v___x_42_);
v_toApplicative_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v___x_43_, 1);
lean_dec(v_unused_109_);
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_108_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_toApplicative_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_108_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_toFunctor_48_; lean_object* v_toSeq_49_; lean_object* v_toSeqLeft_50_; lean_object* v_toSeqRight_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_106_; 
v_toFunctor_48_ = lean_ctor_get(v_toApplicative_44_, 0);
v_toSeq_49_ = lean_ctor_get(v_toApplicative_44_, 2);
v_toSeqLeft_50_ = lean_ctor_get(v_toApplicative_44_, 3);
v_toSeqRight_51_ = lean_ctor_get(v_toApplicative_44_, 4);
v_isSharedCheck_106_ = !lean_is_exclusive(v_toApplicative_44_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v_toApplicative_44_, 1);
lean_dec(v_unused_107_);
v___x_53_ = v_toApplicative_44_;
v_isShared_54_ = v_isSharedCheck_106_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_toSeqRight_51_);
lean_inc(v_toSeqLeft_50_);
lean_inc(v_toSeq_49_);
lean_inc(v_toFunctor_48_);
lean_dec(v_toApplicative_44_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_106_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___f_60_; lean_object* v___f_61_; lean_object* v___f_62_; lean_object* v___x_64_; 
v___f_55_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__3));
v___f_56_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__4));
lean_inc_ref(v_toFunctor_48_);
v___f_57_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_57_, 0, v_toFunctor_48_);
v___f_58_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_58_, 0, v_toFunctor_48_);
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v___f_57_);
lean_ctor_set(v___x_59_, 1, v___f_58_);
v___f_60_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_60_, 0, v_toSeqRight_51_);
v___f_61_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_61_, 0, v_toSeqLeft_50_);
v___f_62_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_62_, 0, v_toSeq_49_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 4, v___f_60_);
lean_ctor_set(v___x_53_, 3, v___f_61_);
lean_ctor_set(v___x_53_, 2, v___f_62_);
lean_ctor_set(v___x_53_, 1, v___f_55_);
lean_ctor_set(v___x_53_, 0, v___x_59_);
v___x_64_ = v___x_53_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___f_55_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v___f_62_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v___f_61_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v___f_60_);
v___x_64_ = v_reuseFailAlloc_105_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_66_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v___f_56_);
lean_ctor_set(v___x_46_, 0, v___x_64_);
v___x_66_ = v___x_46_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v___f_56_);
v___x_66_ = v_reuseFailAlloc_104_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_toApplicative_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_102_; 
v___x_67_ = l_ReaderT_instMonad___redArg(v___x_66_);
v___x_68_ = l_StateRefT_x27_instMonad___redArg(v___x_67_);
v_toApplicative_69_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v___x_68_, 1);
lean_dec(v_unused_103_);
v___x_71_ = v___x_68_;
v_isShared_72_ = v_isSharedCheck_102_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_toApplicative_69_);
lean_dec(v___x_68_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_102_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_toFunctor_73_; lean_object* v_toSeq_74_; lean_object* v_toSeqLeft_75_; lean_object* v_toSeqRight_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_100_; 
v_toFunctor_73_ = lean_ctor_get(v_toApplicative_69_, 0);
v_toSeq_74_ = lean_ctor_get(v_toApplicative_69_, 2);
v_toSeqLeft_75_ = lean_ctor_get(v_toApplicative_69_, 3);
v_toSeqRight_76_ = lean_ctor_get(v_toApplicative_69_, 4);
v_isSharedCheck_100_ = !lean_is_exclusive(v_toApplicative_69_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_dec(v_unused_101_);
v___x_78_ = v_toApplicative_69_;
v_isShared_79_ = v_isSharedCheck_100_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_toSeqRight_76_);
lean_inc(v_toSeqLeft_75_);
lean_inc(v_toSeq_74_);
lean_inc(v_toFunctor_73_);
lean_dec(v_toApplicative_69_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_100_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___f_80_; lean_object* v___f_81_; lean_object* v___f_82_; lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___f_85_; lean_object* v___f_86_; lean_object* v___f_87_; lean_object* v___x_89_; 
v___f_80_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__5));
v___f_81_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___closed__6));
lean_inc_ref(v_toFunctor_73_);
v___f_82_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_82_, 0, v_toFunctor_73_);
v___f_83_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_83_, 0, v_toFunctor_73_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___f_82_);
lean_ctor_set(v___x_84_, 1, v___f_83_);
v___f_85_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_85_, 0, v_toSeqRight_76_);
v___f_86_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_86_, 0, v_toSeqLeft_75_);
v___f_87_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_87_, 0, v_toSeq_74_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 4, v___f_85_);
lean_ctor_set(v___x_78_, 3, v___f_86_);
lean_ctor_set(v___x_78_, 2, v___f_87_);
lean_ctor_set(v___x_78_, 1, v___f_80_);
lean_ctor_set(v___x_78_, 0, v___x_84_);
v___x_89_ = v___x_78_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___f_80_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v___f_87_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v___f_86_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v___f_85_);
v___x_89_ = v_reuseFailAlloc_99_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___f_81_);
lean_ctor_set(v___x_71_, 0, v___x_89_);
v___x_91_ = v___x_71_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_89_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___f_81_);
v___x_91_ = v_reuseFailAlloc_98_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
lean_object* v___x_92_; lean_object* v_toApplicative_93_; lean_object* v_toPure_94_; lean_object* v___x_95_; lean_object* v___x_23920__overap_96_; lean_object* v___x_97_; 
v___x_92_ = l_StateRefT_x27_instMonad___redArg(v___x_91_);
v_toApplicative_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_toApplicative_93_);
lean_dec_ref(v___x_92_);
v_toPure_94_ = lean_ctor_get(v_toApplicative_93_, 1);
lean_inc(v_toPure_94_);
lean_dec_ref(v_toApplicative_93_);
v___x_95_ = l_OptionT_instInhabitedOfPure___redArg(v_toPure_94_);
v___x_23920__overap_96_ = lean_panic_fn_borrowed(v___x_95_, v_msg_8_);
lean_dec(v___x_95_);
lean_inc(v___y_16_);
lean_inc_ref(v___y_15_);
lean_inc(v___y_14_);
lean_inc_ref(v___y_13_);
lean_inc_ref(v___y_12_);
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc(v___y_9_);
v___x_97_ = lean_apply_9(v___x_23920__overap_96_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, lean_box(0));
return v___x_97_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___boxed(lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v_msg_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
return v_res_126_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_130_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2));
v___x_131_ = lean_unsigned_to_nat(34u);
v___x_132_ = lean_unsigned_to_nat(62u);
v___x_133_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1));
v___x_134_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0));
v___x_135_ = l_mkPanicMessageWithDecl(v___x_134_, v___x_133_, v___x_132_, v___x_131_, v___x_130_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object* v_fvarId_136_, lean_object* v_projs_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
uint8_t v___x_150_; lean_object* v___x_151_; 
v___x_150_ = 0;
v___x_151_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_150_, v_fvarId_136_, v_a_143_);
lean_dec(v_fvarId_136_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_315_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_315_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_315_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_315_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
if (lean_obj_tag(v_a_152_) == 1)
{
lean_object* v_val_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_310_; 
v_val_156_ = lean_ctor_get(v_a_152_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_a_152_);
if (v_isSharedCheck_310_ == 0)
{
v___x_158_ = v_a_152_;
v_isShared_159_ = v_isSharedCheck_310_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_val_156_);
lean_dec(v_a_152_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_310_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v_value_160_; 
v_value_160_ = lean_ctor_get(v_val_156_, 3);
lean_inc(v_value_160_);
lean_dec(v_val_156_);
switch(lean_obj_tag(v_value_160_))
{
case 2:
{
lean_object* v_idx_161_; lean_object* v_struct_162_; lean_object* v___x_163_; 
lean_del_object(v___x_158_);
lean_del_object(v___x_154_);
v_idx_161_ = lean_ctor_get(v_value_160_, 1);
lean_inc(v_idx_161_);
v_struct_162_ = lean_ctor_get(v_value_160_, 2);
lean_inc(v_struct_162_);
lean_dec_ref_known(v_value_160_, 3);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v_idx_161_);
lean_ctor_set(v___x_163_, 1, v_projs_137_);
v_fvarId_136_ = v_struct_162_;
v_projs_137_ = v___x_163_;
goto _start;
}
case 3:
{
lean_object* v_declName_165_; lean_object* v_us_166_; lean_object* v_args_167_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; uint8_t v___y_180_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___x_248_; lean_object* v_env_249_; uint8_t v___x_250_; lean_object* v___x_251_; 
v_declName_165_ = lean_ctor_get(v_value_160_, 0);
lean_inc_n(v_declName_165_, 2);
v_us_166_ = lean_ctor_get(v_value_160_, 1);
lean_inc(v_us_166_);
v_args_167_ = lean_ctor_get(v_value_160_, 2);
lean_inc_ref(v_args_167_);
lean_dec_ref_known(v_value_160_, 3);
v___x_248_ = lean_st_ref_get(v_a_145_);
v_env_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_ref(v_env_249_);
lean_dec(v___x_248_);
v___x_250_ = 0;
v___x_251_ = l_Lean_Environment_find_x3f(v_env_249_, v_declName_165_, v___x_250_);
if (lean_obj_tag(v___x_251_) == 1)
{
lean_object* v_val_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_305_; 
v_val_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_305_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_305_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_val_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_305_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
if (lean_obj_tag(v_val_252_) == 6)
{
lean_dec(v_us_166_);
lean_dec(v_declName_165_);
lean_del_object(v___x_154_);
if (lean_obj_tag(v_projs_137_) == 1)
{
lean_object* v_val_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_302_; 
v_val_256_ = lean_ctor_get(v_val_252_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_val_252_);
if (v_isSharedCheck_302_ == 0)
{
v___x_258_ = v_val_252_;
v_isShared_259_ = v_isSharedCheck_302_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_val_256_);
lean_dec(v_val_252_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_302_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_head_260_; lean_object* v_tail_261_; lean_object* v_fvarId_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; lean_object* v___y_271_; lean_object* v_numParams_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_head_260_ = lean_ctor_get(v_projs_137_, 0);
lean_inc(v_head_260_);
v_tail_261_ = lean_ctor_get(v_projs_137_, 1);
lean_inc(v_tail_261_);
lean_dec_ref_known(v_projs_137_, 2);
v_numParams_280_ = lean_ctor_get(v_val_256_, 3);
lean_inc(v_numParams_280_);
lean_dec_ref(v_val_256_);
v___x_281_ = lean_box(0);
v___x_282_ = lean_nat_add(v_numParams_280_, v_head_260_);
lean_dec(v_head_260_);
lean_dec(v_numParams_280_);
v___x_283_ = lean_array_get(v___x_281_, v_args_167_, v___x_282_);
lean_dec(v___x_282_);
lean_dec_ref(v_args_167_);
if (lean_obj_tag(v___x_283_) == 1)
{
lean_object* v_fvarId_284_; 
lean_del_object(v___x_158_);
v_fvarId_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_fvarId_284_);
lean_dec_ref_known(v___x_283_, 1);
v_fvarId_263_ = v_fvarId_284_;
v___y_264_ = v_a_138_;
v___y_265_ = v_a_139_;
v___y_266_ = v_a_140_;
v___y_267_ = v_a_141_;
v___y_268_ = v_a_142_;
v___y_269_ = v_a_143_;
v___y_270_ = v_a_144_;
v___y_271_ = v_a_145_;
goto v___jp_262_;
}
else
{
lean_object* v___x_285_; 
lean_dec(v___x_283_);
v___x_285_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v___x_150_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc_n(v_a_286_, 2);
lean_dec_ref_known(v___x_285_, 1);
v___x_287_ = lean_st_ref_take(v_a_138_);
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 0);
lean_ctor_set(v___x_158_, 0, v_a_286_);
v___x_289_ = v___x_158_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_286_);
v___x_289_ = v_reuseFailAlloc_293_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v_fvarId_292_; 
v___x_290_ = lean_array_push(v___x_287_, v___x_289_);
v___x_291_ = lean_st_ref_set(v_a_138_, v___x_290_);
v_fvarId_292_ = lean_ctor_get(v_a_286_, 0);
lean_inc(v_fvarId_292_);
lean_dec(v_a_286_);
v_fvarId_263_ = v_fvarId_292_;
v___y_264_ = v_a_138_;
v___y_265_ = v_a_139_;
v___y_266_ = v_a_140_;
v___y_267_ = v_a_141_;
v___y_268_ = v_a_142_;
v___y_269_ = v_a_143_;
v___y_270_ = v_a_144_;
v___y_271_ = v_a_145_;
goto v___jp_262_;
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec(v_tail_261_);
lean_del_object(v___x_258_);
lean_del_object(v___x_254_);
lean_del_object(v___x_158_);
v_a_294_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_285_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_285_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
v___jp_262_:
{
uint8_t v___x_272_; 
v___x_272_ = l_List_isEmpty___redArg(v_tail_261_);
if (v___x_272_ == 0)
{
lean_del_object(v___x_258_);
lean_del_object(v___x_254_);
v_fvarId_136_ = v_fvarId_263_;
v_projs_137_ = v_tail_261_;
v_a_138_ = v___y_264_;
v_a_139_ = v___y_265_;
v_a_140_ = v___y_266_;
v_a_141_ = v___y_267_;
v_a_142_ = v___y_268_;
v_a_143_ = v___y_269_;
v_a_144_ = v___y_270_;
v_a_145_ = v___y_271_;
goto _start;
}
else
{
lean_object* v___x_275_; 
lean_dec(v_tail_261_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v_fvarId_263_);
v___x_275_ = v___x_254_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_fvarId_263_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 0);
lean_ctor_set(v___x_258_, 0, v___x_275_);
v___x_277_ = v___x_258_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref_known(v_val_252_, 1);
lean_del_object(v___x_254_);
lean_dec_ref(v_args_167_);
lean_del_object(v___x_158_);
lean_dec(v_projs_137_);
v___x_303_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3, &l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3);
v___x_304_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v___x_303_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
return v___x_304_;
}
}
else
{
lean_del_object(v___x_254_);
lean_dec(v_val_252_);
lean_del_object(v___x_158_);
v___y_200_ = v_a_138_;
v___y_201_ = v_a_139_;
v___y_202_ = v_a_140_;
v___y_203_ = v_a_141_;
v___y_204_ = v_a_142_;
v___y_205_ = v_a_143_;
v___y_206_ = v_a_144_;
v___y_207_ = v_a_145_;
goto v___jp_199_;
}
}
}
else
{
lean_dec(v___x_251_);
lean_del_object(v___x_158_);
v___y_200_ = v_a_138_;
v___y_201_ = v_a_139_;
v___y_202_ = v_a_140_;
v___y_203_ = v_a_141_;
v___y_204_ = v_a_142_;
v___y_205_ = v_a_143_;
v___y_206_ = v_a_144_;
v___y_207_ = v_a_145_;
goto v___jp_199_;
}
v___jp_168_:
{
if (v___y_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec_ref(v___y_179_);
lean_dec_ref(v___y_177_);
lean_dec_ref(v___y_174_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_projs_137_);
v___x_181_ = lean_box(0);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_181_);
v___x_183_ = v___x_154_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_object* v_levelParams_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_del_object(v___x_154_);
v_levelParams_185_ = lean_ctor_get(v___y_179_, 1);
lean_inc(v_levelParams_185_);
lean_dec_ref(v___y_179_);
lean_inc(v_us_166_);
v___x_186_ = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(v___x_150_, v___y_177_, v_us_166_);
v___x_187_ = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(v___y_174_, v_levelParams_185_, v_us_166_);
v___x_188_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v___x_186_, v___x_187_, v_args_167_, v___y_180_, v___y_169_, v___y_173_, v___y_170_, v___y_175_, v___y_178_, v___y_172_, v___y_171_);
lean_dec_ref(v___x_186_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_188_, 1);
v___x_190_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_a_189_, v_projs_137_, v___y_176_, v___y_169_, v___y_173_, v___y_170_, v___y_175_, v___y_178_, v___y_172_, v___y_171_);
return v___x_190_;
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec(v_projs_137_);
v_a_191_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_188_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_188_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
v___jp_199_:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_204_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; uint8_t v___x_210_; lean_object* v___x_211_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref_known(v___x_208_, 1);
v___x_210_ = lean_unbox(v_a_209_);
v___x_211_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_165_, v___x_210_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_231_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_231_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_231_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_231_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
if (lean_obj_tag(v_a_212_) == 1)
{
lean_object* v_val_216_; uint8_t v___x_217_; uint8_t v___x_218_; 
v_val_216_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v_a_212_, 1);
v___x_217_ = lean_unbox(v_a_209_);
lean_dec(v_a_209_);
v___x_218_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v_value_219_; 
v_value_219_ = lean_ctor_get(v_val_216_, 1);
if (lean_obj_tag(v_value_219_) == 0)
{
lean_object* v_toSignature_220_; uint8_t v_recursive_221_; lean_object* v_code_222_; uint8_t v___x_223_; 
lean_del_object(v___x_214_);
v_toSignature_220_ = lean_ctor_get(v_val_216_, 0);
lean_inc_ref(v_toSignature_220_);
v_recursive_221_ = lean_ctor_get_uint8(v_val_216_, sizeof(void*)*3);
v_code_222_ = lean_ctor_get(v_value_219_, 0);
lean_inc_ref(v_code_222_);
v___x_223_ = lean_bool_not(v_recursive_221_);
if (v___x_223_ == 0)
{
v___y_169_ = v___y_201_;
v___y_170_ = v___y_203_;
v___y_171_ = v___y_207_;
v___y_172_ = v___y_206_;
v___y_173_ = v___y_202_;
v___y_174_ = v_code_222_;
v___y_175_ = v___y_204_;
v___y_176_ = v___y_200_;
v___y_177_ = v_val_216_;
v___y_178_ = v___y_205_;
v___y_179_ = v_toSignature_220_;
v___y_180_ = v___x_223_;
goto v___jp_168_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_216_);
v___x_225_ = lean_array_get_size(v_args_167_);
v___x_226_ = lean_nat_dec_eq(v___x_224_, v___x_225_);
lean_dec(v___x_224_);
v___y_169_ = v___y_201_;
v___y_170_ = v___y_203_;
v___y_171_ = v___y_207_;
v___y_172_ = v___y_206_;
v___y_173_ = v___y_202_;
v___y_174_ = v_code_222_;
v___y_175_ = v___y_204_;
v___y_176_ = v___y_200_;
v___y_177_ = v_val_216_;
v___y_178_ = v___y_205_;
v___y_179_ = v_toSignature_220_;
v___y_180_ = v___x_226_;
goto v___jp_168_;
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_229_; 
lean_dec(v_val_216_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_del_object(v___x_154_);
lean_dec(v_projs_137_);
v___x_227_ = lean_box(0);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_227_);
v___x_229_ = v___x_214_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
lean_dec(v_val_216_);
lean_del_object(v___x_214_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_del_object(v___x_154_);
lean_dec(v_projs_137_);
goto v___jp_147_;
}
}
else
{
lean_del_object(v___x_214_);
lean_dec(v_a_212_);
lean_dec(v_a_209_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_del_object(v___x_154_);
lean_dec(v_projs_137_);
goto v___jp_147_;
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec(v_a_209_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_del_object(v___x_154_);
lean_dec(v_projs_137_);
v_a_232_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_211_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_211_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_declName_165_);
lean_del_object(v___x_154_);
lean_dec(v_projs_137_);
v_a_240_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_208_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_208_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
default: 
{
lean_object* v___x_306_; lean_object* v___x_308_; 
lean_dec(v_value_160_);
lean_del_object(v___x_158_);
lean_dec(v_projs_137_);
v___x_306_ = lean_box(0);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_306_);
v___x_308_ = v___x_154_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec(v_a_152_);
lean_dec(v_projs_137_);
v___x_311_ = lean_box(0);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_311_);
v___x_313_ = v___x_154_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_projs_137_);
v_a_316_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_151_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_151_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
v___jp_147_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object* v_code_324_, lean_object* v_projs_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
switch(lean_obj_tag(v_code_324_))
{
case 0:
{
lean_object* v_decl_335_; lean_object* v_k_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_decl_335_ = lean_ctor_get(v_code_324_, 0);
lean_inc_ref(v_decl_335_);
v_k_336_ = lean_ctor_get(v_code_324_, 1);
lean_inc_ref(v_k_336_);
lean_dec_ref_known(v_code_324_, 2);
v___x_337_ = lean_st_ref_take(v_a_326_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_decl_335_);
v___x_339_ = lean_array_push(v___x_337_, v___x_338_);
v___x_340_ = lean_st_ref_set(v_a_326_, v___x_339_);
v_code_324_ = v_k_336_;
goto _start;
}
case 1:
{
lean_object* v_decl_342_; lean_object* v_k_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_decl_342_ = lean_ctor_get(v_code_324_, 0);
lean_inc_ref(v_decl_342_);
v_k_343_ = lean_ctor_get(v_code_324_, 1);
lean_inc_ref(v_k_343_);
lean_dec_ref_known(v_code_324_, 2);
v___x_344_ = lean_st_ref_take(v_a_326_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v_decl_342_);
v___x_346_ = lean_array_push(v___x_344_, v___x_345_);
v___x_347_ = lean_st_ref_set(v_a_326_, v___x_346_);
v_code_324_ = v_k_343_;
goto _start;
}
case 5:
{
lean_object* v_fvarId_349_; lean_object* v___x_350_; 
v_fvarId_349_ = lean_ctor_get(v_code_324_, 0);
lean_inc(v_fvarId_349_);
lean_dec_ref_known(v_code_324_, 1);
v___x_350_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_349_, v_projs_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
return v___x_350_;
}
default: 
{
uint8_t v___x_351_; lean_object* v___x_352_; 
lean_dec(v_projs_325_);
v___x_351_ = 0;
v___x_352_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_351_, v_code_324_, v_a_331_);
lean_dec_ref(v_code_324_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_360_; 
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v___x_352_, 0);
lean_dec(v_unused_361_);
v___x_354_ = v___x_352_;
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
else
{
lean_dec(v___x_352_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_360_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = lean_box(0);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_356_);
v___x_358_ = v___x_354_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_a_362_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_352_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_352_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode___boxed(lean_object* v_code_370_, lean_object* v_projs_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_code_370_, v_projs_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___boxed(lean_object* v_fvarId_382_, lean_object* v_projs_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_382_, v_projs_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
if (lean_obj_tag(v_e_396_) == 2)
{
lean_object* v_idx_405_; lean_object* v_struct_406_; lean_object* v___x_407_; 
v_idx_405_ = lean_ctor_get(v_e_396_, 1);
lean_inc(v_idx_405_);
v_struct_406_ = lean_ctor_get(v_e_396_, 2);
lean_inc_n(v_struct_406_, 2);
v___x_407_ = l_Lean_Compiler_LCNF_getType(v_struct_406_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref_known(v___x_407_, 1);
v___x_409_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_408_, v_a_403_);
lean_dec(v_a_408_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_496_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_496_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_496_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_496_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
if (lean_obj_tag(v_a_410_) == 0)
{
lean_object* v___x_414_; lean_object* v___x_416_; 
lean_dec(v_struct_406_);
lean_dec(v_idx_405_);
lean_dec_ref_known(v_e_396_, 3);
v___x_414_ = lean_box(0);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
uint8_t v___x_418_; lean_object* v___x_419_; 
lean_dec_ref_known(v_a_410_, 1);
lean_del_object(v___x_412_);
v___x_418_ = 0;
v___x_419_ = l_Lean_Compiler_LCNF_LetValue_inferType(v___x_418_, v_e_396_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
v___x_421_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_420_, v_a_403_);
lean_dec(v_a_420_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_479_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_479_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_479_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_479_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
if (lean_obj_tag(v_a_422_) == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_del_object(v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0));
v___x_427_ = lean_st_mk_ref(v___x_426_);
v___x_428_ = lean_box(0);
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v_idx_405_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_struct_406_, v___x_429_, v___x_427_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_466_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_466_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_466_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_466_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_st_ref_get(v___x_427_);
lean_dec(v___x_427_);
if (lean_obj_tag(v_a_431_) == 1)
{
lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_447_; 
v_val_436_ = lean_ctor_get(v_a_431_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_a_431_);
if (v_isSharedCheck_447_ == 0)
{
v___x_438_ = v_a_431_;
v_isShared_439_ = v_isSharedCheck_447_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_dec(v_a_431_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_447_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_435_);
lean_ctor_set(v___x_440_, 1, v_val_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_446_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_444_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_442_);
v___x_444_ = v___x_433_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_object* v___x_448_; 
lean_del_object(v___x_433_);
lean_dec(v_a_431_);
v___x_448_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v___x_418_, v___x_435_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v___x_435_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_456_; 
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_448_, 0);
lean_dec(v_unused_457_);
v___x_450_ = v___x_448_;
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
else
{
lean_dec(v___x_448_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = lean_box(0);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_448_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_448_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v___x_427_);
v_a_467_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_430_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_430_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec_ref_known(v_a_422_, 1);
lean_dec(v_struct_406_);
lean_dec(v_idx_405_);
v___x_475_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_475_);
v___x_477_ = v___x_424_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_struct_406_);
lean_dec(v_idx_405_);
v_a_480_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_421_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_421_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_struct_406_);
lean_dec(v_idx_405_);
v_a_488_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_419_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_419_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec(v_struct_406_);
lean_dec(v_idx_405_);
lean_dec_ref_known(v_e_396_, 3);
v_a_497_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_409_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_409_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_struct_406_);
lean_dec(v_idx_405_);
lean_dec_ref_known(v_e_396_, 3);
v_a_505_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_407_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_407_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_e_396_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___boxed(lean_object* v_e_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_e_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec_ref(v_a_518_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
return v_res_524_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
}
#ifdef __cplusplus
}
#endif
