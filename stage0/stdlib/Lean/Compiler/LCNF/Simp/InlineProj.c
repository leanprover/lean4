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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(lean_object* v_msg_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
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
lean_object* v___x_92_; lean_object* v_toApplicative_93_; lean_object* v_toPure_94_; lean_object* v___x_95_; lean_object* v___x_23363__overap_96_; lean_object* v___x_97_; 
v___x_92_ = l_StateRefT_x27_instMonad___redArg(v___x_91_);
v_toApplicative_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_toApplicative_93_);
lean_dec_ref(v___x_92_);
v_toPure_94_ = lean_ctor_get(v_toApplicative_93_, 1);
lean_inc(v_toPure_94_);
lean_dec_ref(v_toApplicative_93_);
v___x_95_ = l_OptionT_instInhabitedOfPure___redArg(v_toPure_94_);
v___x_23363__overap_96_ = lean_panic_fn_borrowed(v___x_95_, v_msg_8_);
lean_dec(v___x_95_);
lean_inc(v___y_16_);
lean_inc_ref(v___y_15_);
lean_inc(v___y_14_);
lean_inc_ref(v___y_13_);
lean_inc_ref(v___y_12_);
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc(v___y_9_);
v___x_97_ = lean_apply_9(v___x_23363__overap_96_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, lean_box(0));
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
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_8_ = stack[0].m_obj;
lean_object* v___y_9_ = stack[1].m_obj;
lean_object* v___y_10_ = stack[2].m_obj;
lean_object* v___y_11_ = stack[3].m_obj;
lean_object* v___y_12_ = stack[4].m_obj;
lean_object* v___y_13_ = stack[5].m_obj;
lean_object* v___y_14_ = stack[6].m_obj;
lean_object* v___y_15_ = stack[7].m_obj;
lean_object* v___y_16_ = stack[8].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v_msg_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0___boxed(lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
return v_res_127_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_131_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2));
v___x_132_ = lean_unsigned_to_nat(34u);
v___x_133_ = lean_unsigned_to_nat(62u);
v___x_134_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1));
v___x_135_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__0));
v___x_136_ = l_mkPanicMessageWithDecl(v___x_135_, v___x_134_, v___x_133_, v___x_132_, v___x_131_);
return v___x_136_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object* v_fvarId_137_, lean_object* v_projs_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = 0;
v___x_155_ = lean_box(0);
v___x_156_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_154_, v_fvarId_137_, v_a_144_);
lean_dec(v_fvarId_137_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_297_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_297_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_297_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_297_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
if (lean_obj_tag(v_a_157_) == 1)
{
lean_object* v_val_161_; lean_object* v_value_162_; 
v_val_161_ = lean_ctor_get(v_a_157_, 0);
lean_inc(v_val_161_);
lean_dec_ref_known(v_a_157_, 1);
v_value_162_ = lean_ctor_get(v_val_161_, 3);
lean_inc(v_value_162_);
lean_dec(v_val_161_);
switch(lean_obj_tag(v_value_162_))
{
case 2:
{
lean_object* v_idx_163_; lean_object* v_struct_164_; lean_object* v___x_165_; 
lean_del_object(v___x_159_);
v_idx_163_ = lean_ctor_get(v_value_162_, 1);
lean_inc(v_idx_163_);
v_struct_164_ = lean_ctor_get(v_value_162_, 2);
lean_inc(v_struct_164_);
lean_dec_ref_known(v_value_162_, 3);
v___x_165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_165_, 0, v_idx_163_);
lean_ctor_set(v___x_165_, 1, v_projs_138_);
v_fvarId_137_ = v_struct_164_;
v_projs_138_ = v___x_165_;
goto _start;
}
case 3:
{
lean_object* v_declName_167_; lean_object* v_us_168_; lean_object* v_args_169_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___x_232_; lean_object* v_env_233_; uint8_t v___x_234_; lean_object* v___x_235_; 
v_declName_167_ = lean_ctor_get(v_value_162_, 0);
lean_inc_n(v_declName_167_, 2);
v_us_168_ = lean_ctor_get(v_value_162_, 1);
lean_inc(v_us_168_);
v_args_169_ = lean_ctor_get(v_value_162_, 2);
lean_inc_ref(v_args_169_);
lean_dec_ref_known(v_value_162_, 3);
v___x_232_ = lean_st_ref_get(v_a_146_);
v_env_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc_ref(v_env_233_);
lean_dec(v___x_232_);
v___x_234_ = 0;
v___x_235_ = l_Lean_Environment_find_x3f(v_env_233_, v_declName_167_, v___x_234_);
if (lean_obj_tag(v___x_235_) == 1)
{
lean_object* v_val_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_288_; 
v_val_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_288_ == 0)
{
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_288_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_val_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_288_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
if (lean_obj_tag(v_val_236_) == 6)
{
lean_dec(v_us_168_);
lean_dec(v_declName_167_);
if (lean_obj_tag(v_projs_138_) == 1)
{
lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_285_; 
v_val_240_ = lean_ctor_get(v_val_236_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_val_236_);
if (v_isSharedCheck_285_ == 0)
{
v___x_242_ = v_val_236_;
v_isShared_243_ = v_isSharedCheck_285_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_dec(v_val_236_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_285_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_head_244_; lean_object* v_tail_245_; lean_object* v_fvarId_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v_numParams_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_head_244_ = lean_ctor_get(v_projs_138_, 0);
lean_inc(v_head_244_);
v_tail_245_ = lean_ctor_get(v_projs_138_, 1);
lean_inc(v_tail_245_);
lean_dec_ref_known(v_projs_138_, 2);
v_numParams_264_ = lean_ctor_get(v_val_240_, 3);
lean_inc(v_numParams_264_);
lean_dec_ref(v_val_240_);
v___x_265_ = lean_nat_add(v_numParams_264_, v_head_244_);
lean_dec(v_head_244_);
lean_dec(v_numParams_264_);
v___x_266_ = lean_array_get(v___x_155_, v_args_169_, v___x_265_);
lean_dec(v___x_265_);
lean_dec_ref(v_args_169_);
if (lean_obj_tag(v___x_266_) == 1)
{
lean_object* v_fvarId_267_; 
lean_del_object(v___x_242_);
v_fvarId_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_fvarId_267_);
lean_dec_ref_known(v___x_266_, 1);
v_fvarId_247_ = v_fvarId_267_;
v___y_248_ = v_a_139_;
v___y_249_ = v_a_140_;
v___y_250_ = v_a_141_;
v___y_251_ = v_a_142_;
v___y_252_ = v_a_143_;
v___y_253_ = v_a_144_;
v___y_254_ = v_a_145_;
v___y_255_ = v_a_146_;
goto v___jp_246_;
}
else
{
lean_object* v___x_268_; 
lean_dec(v___x_266_);
v___x_268_ = l_Lean_Compiler_LCNF_mkLetDeclErased(v___x_154_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc_n(v_a_269_, 2);
lean_dec_ref_known(v___x_268_, 1);
v___x_270_ = lean_st_ref_take(v_a_139_);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v_a_269_);
v___x_272_ = v___x_242_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_269_);
v___x_272_ = v_reuseFailAlloc_276_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_fvarId_275_; 
v___x_273_ = lean_array_push(v___x_270_, v___x_272_);
v___x_274_ = lean_st_ref_put(v_a_139_, v___x_273_);
v_fvarId_275_ = lean_ctor_get(v_a_269_, 0);
lean_inc(v_fvarId_275_);
lean_dec(v_a_269_);
v_fvarId_247_ = v_fvarId_275_;
v___y_248_ = v_a_139_;
v___y_249_ = v_a_140_;
v___y_250_ = v_a_141_;
v___y_251_ = v_a_142_;
v___y_252_ = v_a_143_;
v___y_253_ = v_a_144_;
v___y_254_ = v_a_145_;
v___y_255_ = v_a_146_;
goto v___jp_246_;
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_tail_245_);
lean_del_object(v___x_242_);
lean_del_object(v___x_238_);
lean_del_object(v___x_159_);
v_a_277_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_268_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_268_);
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
v___jp_246_:
{
uint8_t v___x_256_; 
v___x_256_ = l_List_isEmpty___redArg(v_tail_245_);
if (v___x_256_ == 0)
{
lean_del_object(v___x_238_);
lean_del_object(v___x_159_);
v_fvarId_137_ = v_fvarId_247_;
v_projs_138_ = v_tail_245_;
v_a_139_ = v___y_248_;
v_a_140_ = v___y_249_;
v_a_141_ = v___y_250_;
v_a_142_ = v___y_251_;
v_a_143_ = v___y_252_;
v_a_144_ = v___y_253_;
v_a_145_ = v___y_254_;
v_a_146_ = v___y_255_;
goto _start;
}
else
{
lean_object* v___x_259_; 
lean_dec(v_tail_245_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v_fvarId_247_);
v___x_259_ = v___x_238_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_fvarId_247_);
v___x_259_ = v_reuseFailAlloc_263_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_261_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_259_);
v___x_261_ = v___x_159_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
}
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref_known(v_val_236_, 1);
lean_del_object(v___x_238_);
lean_dec_ref(v_args_169_);
lean_del_object(v___x_159_);
lean_dec(v_projs_138_);
v___x_286_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3, &l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3_once, _init_l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3);
v___x_287_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_spec__0(v___x_286_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
return v___x_287_;
}
}
else
{
lean_del_object(v___x_238_);
lean_dec(v_val_236_);
lean_del_object(v___x_159_);
v___y_171_ = v_a_139_;
v___y_172_ = v_a_140_;
v___y_173_ = v_a_141_;
v___y_174_ = v_a_142_;
v___y_175_ = v_a_143_;
v___y_176_ = v_a_144_;
v___y_177_ = v_a_145_;
v___y_178_ = v_a_146_;
goto v___jp_170_;
}
}
}
else
{
lean_dec(v___x_235_);
lean_del_object(v___x_159_);
v___y_171_ = v_a_139_;
v___y_172_ = v_a_140_;
v___y_173_ = v_a_141_;
v___y_174_ = v_a_142_;
v___y_175_ = v_a_143_;
v___y_176_ = v_a_144_;
v___y_177_ = v_a_145_;
v___y_178_ = v_a_146_;
goto v___jp_170_;
}
v___jp_170_:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Compiler_LCNF_getPhase___redArg(v___y_175_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; uint8_t v___x_181_; lean_object* v___x_182_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = lean_unbox(v_a_180_);
v___x_182_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_167_, v___x_181_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_215_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_215_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_215_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_215_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
if (lean_obj_tag(v_a_183_) == 1)
{
lean_object* v_val_187_; uint8_t v___x_188_; uint8_t v___x_189_; 
v_val_187_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_val_187_);
lean_dec_ref_known(v_a_183_, 1);
v___x_188_ = lean_unbox(v_a_180_);
lean_dec(v_a_180_);
v___x_189_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_188_);
if (v___x_189_ == 0)
{
lean_object* v_value_190_; 
v_value_190_ = lean_ctor_get(v_val_187_, 1);
if (lean_obj_tag(v_value_190_) == 0)
{
uint8_t v_recursive_191_; 
lean_del_object(v___x_185_);
v_recursive_191_ = lean_ctor_get_uint8(v_val_187_, sizeof(void*)*3);
if (v_recursive_191_ == 0)
{
lean_object* v_toSignature_192_; lean_object* v_code_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_toSignature_192_ = lean_ctor_get(v_val_187_, 0);
v_code_193_ = lean_ctor_get(v_value_190_, 0);
lean_inc_ref(v_code_193_);
v___x_194_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_187_);
v___x_195_ = lean_array_get_size(v_args_169_);
v___x_196_ = lean_nat_dec_eq(v___x_194_, v___x_195_);
lean_dec(v___x_194_);
if (v___x_196_ == 0)
{
lean_dec_ref(v_code_193_);
lean_dec(v_val_187_);
lean_dec_ref(v_args_169_);
lean_dec(v_us_168_);
lean_dec(v_projs_138_);
goto v___jp_148_;
}
else
{
lean_object* v_levelParams_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_levelParams_197_ = lean_ctor_get(v_toSignature_192_, 1);
lean_inc(v_levelParams_197_);
lean_inc(v_us_168_);
v___x_198_ = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(v___x_154_, v_val_187_, v_us_168_);
v___x_199_ = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams(v_code_193_, v_levelParams_197_, v_us_168_);
v___x_200_ = l_Lean_Compiler_LCNF_Simp_betaReduce(v___x_198_, v___x_199_, v_args_169_, v___x_196_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec_ref(v___x_198_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_202_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v___x_202_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_a_201_, v_projs_138_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
return v___x_202_;
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec(v_projs_138_);
v_a_203_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_200_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_200_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
else
{
lean_dec(v_val_187_);
lean_dec_ref(v_args_169_);
lean_dec(v_us_168_);
lean_dec(v_projs_138_);
goto v___jp_148_;
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec(v_val_187_);
lean_dec_ref(v_args_169_);
lean_dec(v_us_168_);
lean_dec(v_projs_138_);
v___x_211_ = lean_box(0);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_211_);
v___x_213_ = v___x_185_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_dec(v_val_187_);
lean_del_object(v___x_185_);
lean_dec_ref(v_args_169_);
lean_dec(v_us_168_);
lean_dec(v_projs_138_);
goto v___jp_151_;
}
}
else
{
lean_del_object(v___x_185_);
lean_dec(v_a_183_);
lean_dec(v_a_180_);
lean_dec_ref(v_args_169_);
lean_dec(v_us_168_);
lean_dec(v_projs_138_);
goto v___jp_151_;
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec(v_a_180_);
lean_dec_ref(v_args_169_);
lean_dec(v_us_168_);
lean_dec(v_projs_138_);
v_a_216_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_182_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_182_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v_args_169_);
lean_dec(v_us_168_);
lean_dec(v_declName_167_);
lean_dec(v_projs_138_);
v_a_224_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_179_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_179_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
default: 
{
lean_object* v___x_289_; lean_object* v___x_291_; 
lean_dec(v_value_162_);
lean_dec(v_projs_138_);
v___x_289_ = lean_box(0);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_289_);
v___x_291_ = v___x_159_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec(v_a_157_);
lean_dec(v_projs_138_);
v___x_293_ = lean_box(0);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_293_);
v___x_295_ = v___x_159_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_projs_138_);
v_a_298_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_156_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_156_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
v___jp_148_:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_box(0);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
v___jp_151_:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_box(0);
v___x_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_137_ = stack[0].m_obj;
lean_object* v_projs_138_ = stack[1].m_obj;
lean_object* v_a_139_ = stack[2].m_obj;
lean_object* v_a_140_ = stack[3].m_obj;
lean_object* v_a_141_ = stack[4].m_obj;
lean_object* v_a_142_ = stack[5].m_obj;
lean_object* v_a_143_ = stack[6].m_obj;
lean_object* v_a_144_ = stack[7].m_obj;
lean_object* v_a_145_ = stack[8].m_obj;
lean_object* v_a_146_ = stack[9].m_obj;
lean_object* v_res_306_;
v_res_306_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_137_, v_projs_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
stack->m_obj
 = v_res_306_;
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object* v_code_307_, lean_object* v_projs_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
switch(lean_obj_tag(v_code_307_))
{
case 0:
{
lean_object* v_decl_318_; lean_object* v_k_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_decl_318_ = lean_ctor_get(v_code_307_, 0);
lean_inc_ref(v_decl_318_);
v_k_319_ = lean_ctor_get(v_code_307_, 1);
lean_inc_ref(v_k_319_);
lean_dec_ref_known(v_code_307_, 2);
v___x_320_ = lean_st_ref_take(v_a_309_);
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v_decl_318_);
v___x_322_ = lean_array_push(v___x_320_, v___x_321_);
v___x_323_ = lean_st_ref_put(v_a_309_, v___x_322_);
v_code_307_ = v_k_319_;
goto _start;
}
case 1:
{
lean_object* v_decl_325_; lean_object* v_k_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_decl_325_ = lean_ctor_get(v_code_307_, 0);
lean_inc_ref(v_decl_325_);
v_k_326_ = lean_ctor_get(v_code_307_, 1);
lean_inc_ref(v_k_326_);
lean_dec_ref_known(v_code_307_, 2);
v___x_327_ = lean_st_ref_take(v_a_309_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_decl_325_);
v___x_329_ = lean_array_push(v___x_327_, v___x_328_);
v___x_330_ = lean_st_ref_put(v_a_309_, v___x_329_);
v_code_307_ = v_k_326_;
goto _start;
}
case 5:
{
lean_object* v_fvarId_332_; lean_object* v___x_333_; 
v_fvarId_332_ = lean_ctor_get(v_code_307_, 0);
lean_inc(v_fvarId_332_);
lean_dec_ref_known(v_code_307_, 1);
v___x_333_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_332_, v_projs_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
return v___x_333_;
}
default: 
{
uint8_t v___x_334_; lean_object* v___x_335_; 
lean_dec(v_projs_308_);
v___x_334_ = 0;
v___x_335_ = l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_334_, v_code_307_, v_a_314_);
lean_dec_ref(v_code_307_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v___x_335_, 0);
lean_dec(v_unused_344_);
v___x_337_ = v___x_335_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_dec(v___x_335_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_box(0);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_335_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_335_);
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
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_307_ = stack[0].m_obj;
lean_object* v_projs_308_ = stack[1].m_obj;
lean_object* v_a_309_ = stack[2].m_obj;
lean_object* v_a_310_ = stack[3].m_obj;
lean_object* v_a_311_ = stack[4].m_obj;
lean_object* v_a_312_ = stack[5].m_obj;
lean_object* v_a_313_ = stack[6].m_obj;
lean_object* v_a_314_ = stack[7].m_obj;
lean_object* v_a_315_ = stack[8].m_obj;
lean_object* v_a_316_ = stack[9].m_obj;
lean_object* v_res_353_;
v_res_353_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_code_307_, v_projs_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode___boxed(lean_object* v_code_354_, lean_object* v_projs_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(v_code_354_, v_projs_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___boxed(lean_object* v_fvarId_366_, lean_object* v_projs_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_fvarId_366_, v_projs_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
return v_res_377_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object* v_e_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
if (lean_obj_tag(v_e_380_) == 2)
{
lean_object* v_idx_389_; lean_object* v_struct_390_; lean_object* v___x_391_; 
v_idx_389_ = lean_ctor_get(v_e_380_, 1);
lean_inc(v_idx_389_);
v_struct_390_ = lean_ctor_get(v_e_380_, 2);
lean_inc_n(v_struct_390_, 2);
v___x_391_ = l_Lean_Compiler_LCNF_getType(v_struct_390_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v___x_393_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_392_, v_a_387_);
lean_dec(v_a_392_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_480_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_480_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_480_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_480_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
if (lean_obj_tag(v_a_394_) == 0)
{
lean_object* v___x_398_; lean_object* v___x_400_; 
lean_dec(v_struct_390_);
lean_dec_ref_known(v_e_380_, 3);
lean_dec(v_idx_389_);
v___x_398_ = lean_box(0);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
else
{
uint8_t v___x_402_; lean_object* v___x_403_; 
lean_dec_ref_known(v_a_394_, 1);
lean_del_object(v___x_396_);
v___x_402_ = 0;
v___x_403_ = l_Lean_Compiler_LCNF_LetValue_inferType(v___x_402_, v_e_380_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_405_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = l_Lean_Compiler_LCNF_isClass_x3f___redArg(v_a_404_, v_a_387_);
lean_dec(v_a_404_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_463_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_463_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_463_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_463_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
if (lean_obj_tag(v_a_406_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_del_object(v___x_408_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_411_, 0, v_idx_389_);
lean_ctor_set(v___x_411_, 1, v___x_410_);
v___x_412_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___closed__0));
v___x_413_ = lean_st_mk_ref(v___x_412_);
v___x_414_ = l___private_Lean_Compiler_LCNF_Simp_InlineProj_0__Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(v_struct_390_, v___x_411_, v___x_413_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_450_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_450_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_450_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_450_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; 
v___x_419_ = lean_st_ref_get(v___x_413_);
lean_dec(v___x_413_);
if (lean_obj_tag(v_a_415_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_431_; 
v_val_420_ = lean_ctor_get(v_a_415_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_a_415_);
if (v_isSharedCheck_431_ == 0)
{
v___x_422_ = v_a_415_;
v_isShared_423_ = v_isSharedCheck_431_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_val_420_);
lean_dec(v_a_415_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_431_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_419_);
lean_ctor_set(v___x_424_, 1, v_val_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_424_);
v___x_426_ = v___x_422_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_430_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_426_);
v___x_428_ = v___x_417_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v___x_432_; 
lean_del_object(v___x_417_);
lean_dec(v_a_415_);
v___x_432_ = l_Lean_Compiler_LCNF_eraseCodeDecls(v___x_402_, v___x_419_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v___x_419_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_440_; 
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v___x_432_, 0);
lean_dec(v_unused_441_);
v___x_434_ = v___x_432_;
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
else
{
lean_dec(v___x_432_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_440_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_box(0);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_432_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_432_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
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
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v___x_413_);
v_a_451_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_414_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_414_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec_ref_known(v_a_406_, 1);
lean_dec(v_struct_390_);
lean_dec(v_idx_389_);
v___x_459_ = lean_box(0);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_459_);
v___x_461_ = v___x_408_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
else
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
lean_dec(v_struct_390_);
lean_dec(v_idx_389_);
v_a_464_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___x_405_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_405_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_a_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v_struct_390_);
lean_dec(v_idx_389_);
v_a_472_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_403_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_403_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
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
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_struct_390_);
lean_dec_ref_known(v_e_380_, 3);
lean_dec(v_idx_389_);
v_a_481_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_393_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_393_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_496_; 
lean_dec(v_struct_390_);
lean_dec_ref_known(v_e_380_, 3);
lean_dec(v_idx_389_);
v_a_489_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_496_ == 0)
{
v___x_491_ = v___x_391_;
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_391_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_496_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_494_; 
if (v_isShared_492_ == 0)
{
v___x_494_ = v___x_491_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec(v_e_380_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_380_ = stack[0].m_obj;
lean_object* v_a_381_ = stack[1].m_obj;
lean_object* v_a_382_ = stack[2].m_obj;
lean_object* v_a_383_ = stack[3].m_obj;
lean_object* v_a_384_ = stack[4].m_obj;
lean_object* v_a_385_ = stack[5].m_obj;
lean_object* v_a_386_ = stack[6].m_obj;
lean_object* v_a_387_ = stack[7].m_obj;
lean_object* v_res_499_;
v_res_499_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_e_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___boxed(lean_object* v_e_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(v_e_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_509_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
