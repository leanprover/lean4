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
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* v___x_92_; lean_object* v_toApplicative_93_; lean_object* v_toPure_94_; lean_object* v___x_95_; lean_object* v___x_23999__overap_96_; lean_object* v___x_97_; 
v___x_92_ = l_StateRefT_x27_instMonad___redArg(v___x_91_);
v_toApplicative_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_toApplicative_93_);
lean_dec_ref(v___x_92_);
v_toPure_94_ = lean_ctor_get(v_toApplicative_93_, 1);
lean_inc(v_toPure_94_);
lean_dec_ref(v_toApplicative_93_);
v___x_95_ = l_OptionT_instInhabitedOfPure___redArg(v_toPure_94_);
v___x_23999__overap_96_ = lean_panic_fn(v___x_95_, v_msg_8_);
lean_inc(v___y_16_);
lean_inc_ref(v___y_15_);
lean_inc(v___y_14_);
lean_inc_ref(v___y_13_);
lean_inc_ref(v___y_12_);
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc(v___y_9_);
v___x_97_ = lean_apply_9(v___x_23999__overap_96_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, lean_box(0));
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
uint8_t v___x_153_; lean_object* v___x_154_; 
v___x_153_ = 0;
v___x_154_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_153_, v_fvarId_136_, v_a_143_);
lean_dec(v_fvarId_136_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_296_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_296_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_296_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_296_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
if (lean_obj_tag(v_a_155_) == 1)
{
lean_object* v_val_159_; lean_object* v_value_160_; 
v_val_159_ = lean_ctor_get(v_a_155_, 0);
lean_inc(v_val_159_);
lean_dec_ref(v_a_155_);
v_value_160_ = lean_ctor_get(v_val_159_, 3);
lean_inc(v_value_160_);
lean_dec(v_val_159_);
switch(lean_obj_tag(v_value_160_))
{
case 2:
{
lean_object* v_idx_161_; lean_object* v_struct_162_; lean_object* v___x_163_; 
lean_del_object(v___x_157_);
v_idx_161_ = lean_ctor_get(v_value_160_, 1);
lean_inc(v_idx_161_);
v_struct_162_ = lean_ctor_get(v_value_160_, 2);
lean_inc(v_struct_162_);
lean_dec_ref(v_value_160_);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v_idx_161_);
lean_ctor_set(v___x_163_, 1, v_projs_137_);
v_fvarId_136_ = v_struct_162_;
v_projs_137_ = v___x_163_;
goto _start;
}
case 3:
{
lean_object* v_declName_165_; lean_object* v_us_166_; lean_object* v_args_167_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___x_230_; lean_object* v_env_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v_declName_165_ = lean_ctor_get(v_value_160_, 0);
lean_inc(v_declName_165_);
v_us_166_ = lean_ctor_get(v_value_160_, 1);
lean_inc(v_us_166_);
v_args_167_ = lean_ctor_get(v_value_160_, 2);
lean_inc_ref(v_args_167_);
lean_dec_ref(v_value_160_);
v___x_230_ = lean_st_ref_get(v_a_145_);
v_env_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_env_231_);
lean_dec(v___x_230_);
v___x_232_ = 0;
lean_inc(v_declName_165_);
v___x_233_ = l_Lean_Environment_find_x3f(v_env_231_, v_declName_165_, v___x_232_);
if (lean_obj_tag(v___x_233_) == 1)
{
lean_object* v_val_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_287_; 
v_val_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_287_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_287_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_val_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_287_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
if (lean_obj_tag(v_val_234_) == 6)
{
lean_dec(v_us_166_);
lean_dec(v_declName_165_);
if (lean_obj_tag(v_projs_137_) == 1)
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_284_; 
v_val_238_ = lean_ctor_get(v_val_234_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v_val_234_);
if (v_isSharedCheck_284_ == 0)
{
v___x_240_ = v_val_234_;
v_isShared_241_ = v_isSharedCheck_284_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v_val_234_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_284_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_head_242_; lean_object* v_tail_243_; lean_object* v_fvarId_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v_numParams_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_head_242_ = lean_ctor_get(v_projs_137_, 0);
lean_inc(v_head_242_);
v_tail_243_ = lean_ctor_get(v_projs_137_, 1);
lean_inc(v_tail_243_);
lean_dec_ref(v_projs_137_);
v_numParams_262_ = lean_ctor_get(v_val_238_, 3);
lean_inc(v_numParams_262_);
lean_dec_ref(v_val_238_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_nat_add(v_numParams_262_, v_head_242_);
lean_dec(v_head_242_);
lean_dec(v_numParams_262_);
v___x_265_ = lean_array_get(v___x_263_, v_args_167_, v___x_264_);
lean_dec(v___x_264_);
lean_dec_ref(v_args_167_);
if (lean_obj_tag(v___x_265_) == 1)
{
lean_object* v_fvarId_266_; 
lean_del_object(v___x_240_);
v_fvarId_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_fvarId_266_);
lean_dec_ref(v___x_265_);
v_fvarId_245_ = v_fvarId_266_;
v___y_246_ = v_a_138_;
v___y_247_ = v_a_139_;
v___y_248_ = v_a_140_;
v___y_249_ = v_a_141_;
v___y_250_ = v_a_142_;
v___y_251_ = v_a_143_;
v___y_252_ = v_a_144_;
v___y_253_ = v_a_145_;
goto v___jp_244_;
}
else
{
lean_object* v___x_267_; 
lean_dec(v___x_265_);
v___x_267_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v___x_153_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref(v___x_267_);
v___x_269_ = lean_st_ref_take(v_a_138_);
lean_inc(v_a_268_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 0);
lean_ctor_set(v___x_240_, 0, v_a_268_);
v___x_271_ = v___x_240_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_268_);
v___x_271_ = v_reuseFailAlloc_275_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_fvarId_274_; 
v___x_272_ = lean_array_push(v___x_269_, v___x_271_);
v___x_273_ = lean_st_ref_set(v_a_138_, v___x_272_);
v_fvarId_274_ = lean_ctor_get(v_a_268_, 0);
lean_inc(v_fvarId_274_);
lean_dec(v_a_268_);
v_fvarId_245_ = v_fvarId_274_;
v___y_246_ = v_a_138_;
v___y_247_ = v_a_139_;
v___y_248_ = v_a_140_;
v___y_249_ = v_a_141_;
v___y_250_ = v_a_142_;
v___y_251_ = v_a_143_;
v___y_252_ = v_a_144_;
v___y_253_ = v_a_145_;
goto v___jp_244_;
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec(v_tail_243_);
lean_del_object(v___x_240_);
lean_del_object(v___x_236_);
lean_del_object(v___x_157_);
v_a_276_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_267_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_267_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
v___jp_244_:
{
uint8_t v___x_254_; 
v___x_254_ = l_List_isEmpty___redArg(v_tail_243_);
if (v___x_254_ == 0)
{
lean_del_object(v___x_236_);
lean_del_object(v___x_157_);
v_fvarId_136_ = v_fvarId_245_;
v_projs_137_ = v_tail_243_;
v_a_138_ = v___y_246_;
v_a_139_ = v___y_247_;
v_a_140_ = v___y_248_;
v_a_141_ = v___y_249_;
v_a_142_ = v___y_250_;
v_a_143_ = v___y_251_;
v_a_144_ = v___y_252_;
v_a_145_ = v___y_253_;
goto _start;
}
else
{
lean_object* v___x_257_; 
lean_dec(v_tail_243_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v_fvarId_245_);
v___x_257_ = v___x_236_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_fvarId_245_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_257_);
v___x_259_ = v___x_157_;
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
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec_ref(v_val_234_);
lean_del_object(v___x_236_);
lean_dec_ref(v_args_167_);
lean_del_object(v___x_157_);
lean_dec(v_projs_137_);
v___x_285_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3, &l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3);
v___x_286_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v___x_285_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
return v___x_286_;
}
}
else
{
lean_del_object(v___x_236_);
lean_dec(v_val_234_);
lean_del_object(v___x_157_);
v___y_169_ = v_a_138_;
v___y_170_ = v_a_139_;
v___y_171_ = v_a_140_;
v___y_172_ = v_a_141_;
v___y_173_ = v_a_142_;
v___y_174_ = v_a_143_;
v___y_175_ = v_a_144_;
v___y_176_ = v_a_145_;
goto v___jp_168_;
}
}
}
else
{
lean_dec(v___x_233_);
lean_del_object(v___x_157_);
v___y_169_ = v_a_138_;
v___y_170_ = v_a_139_;
v___y_171_ = v_a_140_;
v___y_172_ = v_a_141_;
v___y_173_ = v_a_142_;
v___y_174_ = v_a_143_;
v___y_175_ = v_a_144_;
v___y_176_ = v_a_145_;
goto v___jp_168_;
}
v___jp_168_:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_173_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; uint8_t v___x_179_; lean_object* v___x_180_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref(v___x_177_);
v___x_179_ = lean_unbox(v_a_178_);
v___x_180_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_165_, v___x_179_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_213_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_213_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_213_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_213_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
if (lean_obj_tag(v_a_181_) == 1)
{
lean_object* v_val_185_; uint8_t v___x_186_; uint8_t v___x_187_; 
v_val_185_ = lean_ctor_get(v_a_181_, 0);
lean_inc(v_val_185_);
lean_dec_ref(v_a_181_);
v___x_186_ = lean_unbox(v_a_178_);
lean_dec(v_a_178_);
v___x_187_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v_value_188_; 
v_value_188_ = lean_ctor_get(v_val_185_, 1);
if (lean_obj_tag(v_value_188_) == 0)
{
uint8_t v_recursive_189_; 
lean_del_object(v___x_183_);
v_recursive_189_ = lean_ctor_get_uint8(v_val_185_, sizeof(void*)*3);
if (v_recursive_189_ == 0)
{
lean_object* v_toSignature_190_; lean_object* v_code_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_toSignature_190_ = lean_ctor_get(v_val_185_, 0);
v_code_191_ = lean_ctor_get(v_value_188_, 0);
lean_inc_ref(v_code_191_);
v___x_192_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_185_);
v___x_193_ = lean_array_get_size(v_args_167_);
v___x_194_ = lean_nat_dec_eq(v___x_192_, v___x_193_);
lean_dec(v___x_192_);
if (v___x_194_ == 0)
{
lean_dec_ref(v_code_191_);
lean_dec(v_val_185_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_projs_137_);
goto v___jp_147_;
}
else
{
lean_object* v_levelParams_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_levelParams_195_ = lean_ctor_get(v_toSignature_190_, 1);
lean_inc(v_levelParams_195_);
lean_inc(v_us_166_);
v___x_196_ = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(v___x_153_, v_val_185_, v_us_166_);
v___x_197_ = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(v_code_191_, v_levelParams_195_, v_us_166_);
v___x_198_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v___x_196_, v___x_197_, v_args_167_, v___x_194_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec_ref(v___x_196_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v___x_198_);
v___x_200_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_a_199_, v_projs_137_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
return v___x_200_;
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_projs_137_);
v_a_201_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_198_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_198_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
else
{
lean_dec(v_val_185_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_projs_137_);
goto v___jp_147_;
}
}
else
{
lean_object* v___x_209_; lean_object* v___x_211_; 
lean_dec(v_val_185_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_projs_137_);
v___x_209_ = lean_box(0);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_209_);
v___x_211_ = v___x_183_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_dec(v_val_185_);
lean_del_object(v___x_183_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_projs_137_);
goto v___jp_150_;
}
}
else
{
lean_del_object(v___x_183_);
lean_dec(v_a_181_);
lean_dec(v_a_178_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_projs_137_);
goto v___jp_150_;
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec(v_a_178_);
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_projs_137_);
v_a_214_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_180_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_180_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_args_167_);
lean_dec(v_us_166_);
lean_dec(v_declName_165_);
lean_dec(v_projs_137_);
v_a_222_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_177_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_177_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
default: 
{
lean_object* v___x_288_; lean_object* v___x_290_; 
lean_dec(v_value_160_);
lean_dec(v_projs_137_);
v___x_288_ = lean_box(0);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_288_);
v___x_290_ = v___x_157_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
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
else
{
lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v_a_155_);
lean_dec(v_projs_137_);
v___x_292_ = lean_box(0);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_292_);
v___x_294_ = v___x_157_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_projs_137_);
v_a_297_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_154_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_154_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
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
v___jp_150_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object* v_code_305_, lean_object* v_projs_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
switch(lean_obj_tag(v_code_305_))
{
case 0:
{
lean_object* v_decl_316_; lean_object* v_k_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_decl_316_ = lean_ctor_get(v_code_305_, 0);
lean_inc_ref(v_decl_316_);
v_k_317_ = lean_ctor_get(v_code_305_, 1);
lean_inc_ref(v_k_317_);
lean_dec_ref(v_code_305_);
v___x_318_ = lean_st_ref_take(v_a_307_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v_decl_316_);
v___x_320_ = lean_array_push(v___x_318_, v___x_319_);
v___x_321_ = lean_st_ref_set(v_a_307_, v___x_320_);
v_code_305_ = v_k_317_;
goto _start;
}
case 1:
{
lean_object* v_decl_323_; lean_object* v_k_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_decl_323_ = lean_ctor_get(v_code_305_, 0);
lean_inc_ref(v_decl_323_);
v_k_324_ = lean_ctor_get(v_code_305_, 1);
lean_inc_ref(v_k_324_);
lean_dec_ref(v_code_305_);
v___x_325_ = lean_st_ref_take(v_a_307_);
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_decl_323_);
v___x_327_ = lean_array_push(v___x_325_, v___x_326_);
v___x_328_ = lean_st_ref_set(v_a_307_, v___x_327_);
v_code_305_ = v_k_324_;
goto _start;
}
case 5:
{
lean_object* v_fvarId_330_; lean_object* v___x_331_; 
v_fvarId_330_ = lean_ctor_get(v_code_305_, 0);
lean_inc(v_fvarId_330_);
lean_dec_ref(v_code_305_);
v___x_331_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_330_, v_projs_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
return v___x_331_;
}
default: 
{
uint8_t v___x_332_; lean_object* v___x_333_; 
lean_dec(v_projs_306_);
v___x_332_ = 0;
v___x_333_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_332_, v_code_305_, v_a_312_);
lean_dec_ref(v_code_305_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; 
v_unused_342_ = lean_ctor_get(v___x_333_, 0);
lean_dec(v_unused_342_);
v___x_335_ = v___x_333_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_dec(v___x_333_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = lean_box(0);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_343_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_333_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_333_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode___boxed(lean_object* v_code_351_, lean_object* v_projs_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_code_351_, v_projs_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___boxed(lean_object* v_fvarId_363_, lean_object* v_projs_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_363_, v_projs_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object* v_e_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
if (lean_obj_tag(v_e_377_) == 2)
{
lean_object* v_idx_386_; lean_object* v_struct_387_; lean_object* v___x_388_; 
v_idx_386_ = lean_ctor_get(v_e_377_, 1);
lean_inc(v_idx_386_);
v_struct_387_ = lean_ctor_get(v_e_377_, 2);
lean_inc(v_struct_387_);
lean_inc(v_struct_387_);
v___x_388_ = l_Lean_Compiler_LCNF_getType(v_struct_387_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref(v___x_388_);
v___x_390_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_389_, v_a_384_);
lean_dec(v_a_389_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_477_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_477_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_477_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_477_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
if (lean_obj_tag(v_a_391_) == 0)
{
lean_object* v___x_395_; lean_object* v___x_397_; 
lean_dec(v_struct_387_);
lean_dec(v_idx_386_);
lean_dec_ref(v_e_377_);
v___x_395_ = lean_box(0);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_395_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
uint8_t v___x_399_; lean_object* v___x_400_; 
lean_dec_ref(v_a_391_);
lean_del_object(v___x_393_);
v___x_399_ = 0;
v___x_400_ = l_Lean_Compiler_LCNF_LetValue_inferType(v___x_399_, v_e_377_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_402_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
v___x_402_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_401_, v_a_384_);
lean_dec(v_a_401_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_460_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_460_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_460_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_460_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
if (lean_obj_tag(v_a_403_) == 0)
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_del_object(v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0));
v___x_408_ = lean_st_mk_ref(v___x_407_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v_idx_386_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_struct_387_, v___x_410_, v___x_408_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_447_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_447_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_447_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_447_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; 
v___x_416_ = lean_st_ref_get(v___x_408_);
lean_dec(v___x_408_);
if (lean_obj_tag(v_a_412_) == 1)
{
lean_object* v_val_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_428_; 
v_val_417_ = lean_ctor_get(v_a_412_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v_a_412_);
if (v_isSharedCheck_428_ == 0)
{
v___x_419_ = v_a_412_;
v_isShared_420_ = v_isSharedCheck_428_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_val_417_);
lean_dec(v_a_412_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_428_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_416_);
lean_ctor_set(v___x_421_, 1, v_val_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_425_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_423_);
v___x_425_ = v___x_414_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
else
{
lean_object* v___x_429_; 
lean_del_object(v___x_414_);
lean_dec(v_a_412_);
v___x_429_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v___x_399_, v___x_416_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v___x_416_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_429_, 0);
lean_dec(v_unused_438_);
v___x_431_ = v___x_429_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_dec(v___x_429_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_box(0);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_a_439_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_429_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_429_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
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
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v___x_408_);
v_a_448_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_411_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_411_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
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
lean_object* v___x_456_; lean_object* v___x_458_; 
lean_dec_ref(v_a_403_);
lean_dec(v_struct_387_);
lean_dec(v_idx_386_);
v___x_456_ = lean_box(0);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_456_);
v___x_458_ = v___x_405_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_struct_387_);
lean_dec(v_idx_386_);
v_a_461_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_402_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_402_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_struct_387_);
lean_dec(v_idx_386_);
v_a_469_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_400_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_400_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec(v_struct_387_);
lean_dec(v_idx_386_);
lean_dec_ref(v_e_377_);
v_a_478_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_390_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_390_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v_struct_387_);
lean_dec(v_idx_386_);
lean_dec_ref(v_e_377_);
v_a_486_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_388_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_388_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v_e_377_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___boxed(lean_object* v_e_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_e_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
return v_res_505_;
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
