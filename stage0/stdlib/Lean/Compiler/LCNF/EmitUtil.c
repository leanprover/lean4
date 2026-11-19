// Lean compiler output
// Module: Lean.Compiler.LCNF.EmitUtil
// Imports: public import Lean.Compiler.LCNF.CompilerM import Lean.Compiler.LCNF.PhaseExt import Lean.Compiler.InitAttr
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_getBuiltinInitFnNameFor_x3f(lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.EmitUtil"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Compiler.LCNF.EmitUtil.0.Lean.Compiler.LCNF.collectUsedDecls.go"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "collectUsedDecls: could not find declaration or signature for '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_collectUsedDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_collectUsedDecls___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_collectUsedDecls___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_collectUsedDecls___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_collectUsedDecls___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_usesModuleFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_usesModuleFrom___boxed(lean_object*, lean_object*);
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(lean_object* v_msg_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v_toApplicative_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_43_; 
v___x_9_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__0);
v___x_10_ = l_StateRefT_x27_instMonad___redArg(v___x_9_);
v_toApplicative_11_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_43_ == 0)
{
lean_object* v_unused_44_; 
v_unused_44_ = lean_ctor_get(v___x_10_, 1);
lean_dec(v_unused_44_);
v___x_13_ = v___x_10_;
v_isShared_14_ = v_isSharedCheck_43_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_toApplicative_11_);
lean_dec(v___x_10_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_43_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_toFunctor_15_; lean_object* v_toSeq_16_; lean_object* v_toSeqLeft_17_; lean_object* v_toSeqRight_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_41_; 
v_toFunctor_15_ = lean_ctor_get(v_toApplicative_11_, 0);
v_toSeq_16_ = lean_ctor_get(v_toApplicative_11_, 2);
v_toSeqLeft_17_ = lean_ctor_get(v_toApplicative_11_, 3);
v_toSeqRight_18_ = lean_ctor_get(v_toApplicative_11_, 4);
v_isSharedCheck_41_ = !lean_is_exclusive(v_toApplicative_11_);
if (v_isSharedCheck_41_ == 0)
{
lean_object* v_unused_42_; 
v_unused_42_ = lean_ctor_get(v_toApplicative_11_, 1);
lean_dec(v_unused_42_);
v___x_20_ = v_toApplicative_11_;
v_isShared_21_ = v_isSharedCheck_41_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_toSeqRight_18_);
lean_inc(v_toSeqLeft_17_);
lean_inc(v_toSeq_16_);
lean_inc(v_toFunctor_15_);
lean_dec(v_toApplicative_11_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_41_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___x_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___x_31_; 
v___f_22_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__1));
v___f_23_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___closed__2));
lean_inc_ref(v_toFunctor_15_);
v___f_24_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_24_, 0, v_toFunctor_15_);
v___f_25_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_25_, 0, v_toFunctor_15_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___f_24_);
lean_ctor_set(v___x_26_, 1, v___f_25_);
v___f_27_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_27_, 0, v_toSeqRight_18_);
v___f_28_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_28_, 0, v_toSeqLeft_17_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_29_, 0, v_toSeq_16_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 4, v___f_27_);
lean_ctor_set(v___x_20_, 3, v___f_28_);
lean_ctor_set(v___x_20_, 2, v___f_29_);
lean_ctor_set(v___x_20_, 1, v___f_22_);
lean_ctor_set(v___x_20_, 0, v___x_26_);
v___x_31_ = v___x_20_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v___f_22_);
lean_ctor_set(v_reuseFailAlloc_40_, 2, v___f_29_);
lean_ctor_set(v_reuseFailAlloc_40_, 3, v___f_28_);
lean_ctor_set(v_reuseFailAlloc_40_, 4, v___f_27_);
v___x_31_ = v_reuseFailAlloc_40_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
lean_object* v___x_33_; 
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___f_23_);
lean_ctor_set(v___x_13_, 0, v___x_31_);
v___x_33_ = v___x_13_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v___f_23_);
v___x_33_ = v_reuseFailAlloc_39_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_5333__overap_37_; lean_object* v___x_38_; 
v___x_34_ = l_StateRefT_x27_instMonad___redArg(v___x_33_);
v___x_35_ = lean_box(0);
v___x_36_ = l_instInhabitedOfMonad___redArg(v___x_34_, v___x_35_);
v___x_5333__overap_37_ = lean_panic_fn_borrowed(v___x_36_, v_msg_4_);
lean_dec(v___x_36_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
v___x_38_ = lean_apply_4(v___x_5333__overap_37_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_38_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v_msg_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(lean_object* v_f_51_, lean_object* v_v_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
if (lean_obj_tag(v_v_52_) == 0)
{
lean_object* v_code_57_; lean_object* v___x_58_; 
v_code_57_ = lean_ctor_get(v_v_52_, 0);
lean_inc_ref(v_code_57_);
lean_dec_ref_known(v_v_52_, 1);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
v___x_58_ = lean_apply_5(v_f_51_, v_code_57_, v___y_53_, v___y_54_, v___y_55_, lean_box(0));
return v___x_58_;
}
else
{
lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_66_; 
lean_dec_ref(v_f_51_);
v_isSharedCheck_66_ = !lean_is_exclusive(v_v_52_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v_v_52_, 0);
lean_dec(v_unused_67_);
v___x_60_ = v_v_52_;
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
else
{
lean_dec(v_v_52_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_66_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
if (v_isShared_61_ == 0)
{
lean_ctor_set_tag(v___x_60_, 0);
lean_ctor_set(v___x_60_, 0, v___x_62_);
v___x_64_ = v___x_60_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg___boxed(lean_object* v_f_68_, lean_object* v_v_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_68_, v_v_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed(lean_object* v___x_75_, lean_object* v_x_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v___x_6154__boxed_81_; lean_object* v_res_82_; 
v___x_6154__boxed_81_ = lean_unbox(v___x_75_);
v_res_82_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(v___x_6154__boxed_81_, v_x_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(lean_object* v_as_87_, size_t v_i_88_, size_t v_stop_89_, lean_object* v_b_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_a_96_; lean_object* v___y_101_; uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_eq(v_i_88_, v_stop_89_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_visited_106_; uint8_t v___x_107_; 
v___x_104_ = lean_array_uget_borrowed(v_as_87_, v_i_88_);
v___x_105_ = lean_st_ref_get(v___y_91_);
v_visited_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_visited_106_);
lean_dec(v___x_105_);
v___x_107_ = l_Lean_NameSet_contains(v_visited_106_, v___x_104_);
lean_dec(v_visited_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v_visited_109_; lean_object* v_localDecls_110_; lean_object* v_extSigs_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_201_; 
v___x_108_ = lean_st_ref_take(v___y_91_);
v_visited_109_ = lean_ctor_get(v___x_108_, 0);
v_localDecls_110_ = lean_ctor_get(v___x_108_, 1);
v_extSigs_111_ = lean_ctor_get(v___x_108_, 2);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_201_ == 0)
{
v___x_113_ = v___x_108_;
v_isShared_114_ = v_isSharedCheck_201_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_extSigs_111_);
lean_inc(v_localDecls_110_);
lean_inc(v_visited_109_);
lean_dec(v___x_108_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_201_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_inc(v___x_104_);
v___x_115_ = l_Lean_NameSet_insert(v_visited_109_, v___x_104_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_115_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_localDecls_110_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_extSigs_111_);
v___x_117_ = v_reuseFailAlloc_200_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_st_ref_put(v___y_91_, v___x_117_);
v___x_119_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v___x_104_, v___y_93_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref_known(v___x_119_, 1);
if (lean_obj_tag(v_a_120_) == 1)
{
lean_object* v_val_121_; lean_object* v___x_122_; lean_object* v_visited_123_; lean_object* v_localDecls_124_; lean_object* v_extSigs_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_154_; 
v_val_121_ = lean_ctor_get(v_a_120_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v_a_120_, 1);
v___x_122_ = lean_st_ref_take(v___y_91_);
v_visited_123_ = lean_ctor_get(v___x_122_, 0);
v_localDecls_124_ = lean_ctor_get(v___x_122_, 1);
v_extSigs_125_ = lean_ctor_get(v___x_122_, 2);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_154_ == 0)
{
v___x_127_ = v___x_122_;
v_isShared_128_ = v_isSharedCheck_154_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_extSigs_125_);
lean_inc(v_localDecls_124_);
lean_inc(v_visited_123_);
lean_dec(v___x_122_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_154_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
lean_inc(v_val_121_);
v___x_129_ = lean_array_push(v_localDecls_124_, v_val_121_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_visited_123_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_extSigs_125_);
v___x_131_ = v_reuseFailAlloc_153_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v_toSignature_133_; lean_object* v_value_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___f_137_; lean_object* v___x_138_; 
v___x_132_ = lean_st_ref_put(v___y_91_, v___x_131_);
v_toSignature_133_ = lean_ctor_get(v_val_121_, 0);
lean_inc_ref(v_toSignature_133_);
v_value_134_ = lean_ctor_get(v_val_121_, 1);
lean_inc_ref(v_value_134_);
lean_dec(v_val_121_);
v___x_135_ = 1;
v___x_136_ = lean_box(v___x_135_);
v___f_137_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed), 6, 1);
lean_closure_set(v___f_137_, 0, v___x_136_);
v___x_138_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v___f_137_, v_value_134_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v___x_139_; lean_object* v_val_141_; lean_object* v_env_146_; lean_object* v_name_147_; lean_object* v___x_148_; 
lean_dec_ref_known(v___x_138_, 1);
v___x_139_ = lean_st_ref_get(v___y_93_);
v_env_146_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref_n(v_env_146_, 2);
lean_dec(v___x_139_);
v_name_147_ = lean_ctor_get(v_toSignature_133_, 0);
lean_inc_n(v_name_147_, 2);
lean_dec_ref(v_toSignature_133_);
v___x_148_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_146_, v_name_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v___x_149_; 
v___x_149_ = lean_get_init_fn_name_for(v_env_146_, v_name_147_);
if (lean_obj_tag(v___x_149_) == 1)
{
lean_object* v_val_150_; 
v_val_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_val_150_);
lean_dec_ref_known(v___x_149_, 1);
v_val_141_ = v_val_150_;
goto v___jp_140_;
}
else
{
lean_object* v___x_151_; 
lean_dec(v___x_149_);
v___x_151_ = lean_box(0);
v_a_96_ = v___x_151_;
goto v___jp_95_;
}
}
else
{
lean_object* v_val_152_; 
lean_dec(v_name_147_);
lean_dec_ref(v_env_146_);
v_val_152_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_val_152_);
lean_dec_ref_known(v___x_148_, 1);
v_val_141_ = v_val_152_;
goto v___jp_140_;
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = lean_mk_empty_array_with_capacity(v___x_142_);
v___x_144_ = lean_array_push(v___x_143_, v_val_141_);
v___x_145_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_144_, v___y_91_, v___y_92_, v___y_93_);
lean_dec_ref(v___x_144_);
v___y_101_ = v___x_145_;
goto v___jp_100_;
}
}
else
{
lean_dec_ref(v_toSignature_133_);
return v___x_138_;
}
}
}
}
else
{
lean_object* v___x_155_; 
lean_dec(v_a_120_);
lean_inc(v___x_104_);
v___x_155_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v___x_104_, v___y_93_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref_known(v___x_155_, 1);
if (lean_obj_tag(v_a_156_) == 1)
{
lean_object* v_val_157_; lean_object* v___x_158_; lean_object* v_visited_159_; lean_object* v_localDecls_160_; lean_object* v_extSigs_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_171_; 
v_val_157_ = lean_ctor_get(v_a_156_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v_a_156_, 1);
v___x_158_ = lean_st_ref_take(v___y_91_);
v_visited_159_ = lean_ctor_get(v___x_158_, 0);
v_localDecls_160_ = lean_ctor_get(v___x_158_, 1);
v_extSigs_161_ = lean_ctor_get(v___x_158_, 2);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_171_ == 0)
{
v___x_163_ = v___x_158_;
v_isShared_164_ = v_isSharedCheck_171_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_extSigs_161_);
lean_inc(v_localDecls_160_);
lean_inc(v_visited_159_);
lean_dec(v___x_158_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_171_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_array_push(v_extSigs_161_, v_val_157_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 2, v___x_166_);
v___x_168_ = v___x_163_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_visited_159_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_localDecls_160_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v___x_166_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; 
v___x_169_ = lean_st_ref_put(v___y_91_, v___x_168_);
v_a_96_ = v___x_165_;
goto v___jp_95_;
}
}
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_a_156_);
v___x_172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0));
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1));
v___x_174_ = lean_unsigned_to_nat(42u);
v___x_175_ = lean_unsigned_to_nat(8u);
v___x_176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2));
v___x_177_ = 1;
lean_inc(v___x_104_);
v___x_178_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_104_, v___x_177_);
v___x_179_ = lean_string_append(v___x_176_, v___x_178_);
lean_dec_ref(v___x_178_);
v___x_180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3));
v___x_181_ = lean_string_append(v___x_179_, v___x_180_);
v___x_182_ = l_mkPanicMessageWithDecl(v___x_172_, v___x_173_, v___x_174_, v___x_175_, v___x_181_);
lean_dec_ref(v___x_181_);
v___x_183_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v___x_182_, v___y_91_, v___y_92_, v___y_93_);
v___y_101_ = v___x_183_;
goto v___jp_100_;
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_155_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_155_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_119_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_119_);
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
}
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(0);
v_a_96_ = v___x_202_;
goto v___jp_95_;
}
}
else
{
lean_object* v___x_203_; 
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_b_90_);
return v___x_203_;
}
v___jp_95_:
{
size_t v___x_97_; size_t v___x_98_; 
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_add(v_i_88_, v___x_97_);
v_i_88_ = v___x_98_;
v_b_90_ = v_a_96_;
goto _start;
}
v___jp_100_:
{
if (lean_obj_tag(v___y_101_) == 0)
{
lean_object* v_a_102_; 
v_a_102_ = lean_ctor_get(v___y_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___y_101_, 1);
v_a_96_ = v_a_102_;
goto v___jp_95_;
}
else
{
return v___y_101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(lean_object* v_names_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_array_get_size(v_names_204_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
return v___x_213_;
}
else
{
size_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = ((size_t)0ULL);
v___x_215_ = lean_usize_of_nat(v___x_210_);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_204_, v___x_214_, v___x_215_, v___x_211_, v_a_205_, v_a_206_, v_a_207_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(lean_object* v_code_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_declName_223_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; 
if (lean_obj_tag(v_code_217_) == 0)
{
lean_object* v_decl_231_; lean_object* v_value_232_; 
v_decl_231_ = lean_ctor_get(v_code_217_, 0);
lean_inc_ref(v_decl_231_);
lean_dec_ref_known(v_code_217_, 2);
v_value_232_ = lean_ctor_get(v_decl_231_, 3);
lean_inc(v_value_232_);
lean_dec_ref(v_decl_231_);
switch(lean_obj_tag(v_value_232_))
{
case 3:
{
lean_object* v_declName_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_declName_233_ = lean_ctor_get(v_value_232_, 0);
lean_inc(v_declName_233_);
lean_dec_ref_known(v_value_232_, 3);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_mk_empty_array_with_capacity(v___x_234_);
v___x_236_ = lean_array_push(v___x_235_, v_declName_233_);
v___x_237_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_236_, v_a_218_, v_a_219_, v_a_220_);
lean_dec_ref(v___x_236_);
return v___x_237_;
}
case 9:
{
lean_object* v_fn_238_; 
v_fn_238_ = lean_ctor_get(v_value_232_, 0);
lean_inc(v_fn_238_);
lean_dec_ref_known(v_value_232_, 2);
v_declName_223_ = v_fn_238_;
v___y_224_ = v_a_218_;
v___y_225_ = v_a_219_;
v___y_226_ = v_a_220_;
goto v___jp_222_;
}
case 10:
{
lean_object* v_fn_239_; 
v_fn_239_ = lean_ctor_get(v_value_232_, 0);
lean_inc(v_fn_239_);
lean_dec_ref_known(v_value_232_, 2);
v_declName_223_ = v_fn_239_;
v___y_224_ = v_a_218_;
v___y_225_ = v_a_219_;
v___y_226_ = v_a_220_;
goto v___jp_222_;
}
default: 
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_value_232_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v_code_217_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
v___jp_222_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_mk_empty_array_with_capacity(v___x_227_);
v___x_229_ = lean_array_push(v___x_228_, v_declName_223_);
v___x_230_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_229_, v___y_224_, v___y_225_, v___y_226_);
lean_dec_ref(v___x_229_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(uint8_t v_pu_244_, lean_object* v_as_245_, size_t v_i_246_, size_t v_stop_247_, lean_object* v_b_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___y_254_; uint8_t v___x_259_; 
v___x_259_ = lean_usize_dec_eq(v_i_246_, v_stop_247_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
v___x_260_ = lean_array_uget_borrowed(v_as_245_, v_i_246_);
switch(lean_obj_tag(v___x_260_))
{
case 0:
{
lean_object* v_code_261_; lean_object* v___x_262_; 
v_code_261_ = lean_ctor_get(v___x_260_, 2);
lean_inc_ref(v_code_261_);
v___x_262_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_244_, v_code_261_, v___y_249_, v___y_250_, v___y_251_);
v___y_254_ = v___x_262_;
goto v___jp_253_;
}
case 1:
{
lean_object* v_code_263_; lean_object* v___x_264_; 
v_code_263_ = lean_ctor_get(v___x_260_, 1);
lean_inc_ref(v_code_263_);
v___x_264_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_244_, v_code_263_, v___y_249_, v___y_250_, v___y_251_);
v___y_254_ = v___x_264_;
goto v___jp_253_;
}
default: 
{
lean_object* v_code_265_; lean_object* v___x_266_; 
v_code_265_ = lean_ctor_get(v___x_260_, 0);
lean_inc_ref(v_code_265_);
v___x_266_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_244_, v_code_265_, v___y_249_, v___y_250_, v___y_251_);
v___y_254_ = v___x_266_;
goto v___jp_253_;
}
}
}
else
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_b_248_);
return v___x_267_;
}
v___jp_253_:
{
if (lean_obj_tag(v___y_254_) == 0)
{
lean_object* v_a_255_; size_t v___x_256_; size_t v___x_257_; 
v_a_255_ = lean_ctor_get(v___y_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___y_254_, 1);
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_add(v_i_246_, v___x_256_);
v_i_246_ = v___x_257_;
v_b_248_ = v_a_255_;
goto _start;
}
else
{
return v___y_254_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(uint8_t v_pu_268_, lean_object* v_c_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; 
lean_inc_ref(v_c_269_);
v___x_274_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_c_269_, v___y_270_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_320_; 
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_274_, 0);
lean_dec(v_unused_321_);
v___x_276_ = v___x_274_;
v_isShared_277_ = v_isSharedCheck_320_;
goto v_resetjp_275_;
}
else
{
lean_dec(v___x_274_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_320_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
switch(lean_obj_tag(v_c_269_))
{
case 0:
{
lean_object* v_k_278_; 
lean_del_object(v___x_276_);
v_k_278_ = lean_ctor_get(v_c_269_, 1);
lean_inc_ref(v_k_278_);
lean_dec_ref_known(v_c_269_, 2);
v_c_269_ = v_k_278_;
goto _start;
}
case 1:
{
lean_object* v_decl_280_; lean_object* v_k_281_; lean_object* v_value_282_; lean_object* v___x_283_; 
lean_del_object(v___x_276_);
v_decl_280_ = lean_ctor_get(v_c_269_, 0);
lean_inc_ref(v_decl_280_);
v_k_281_ = lean_ctor_get(v_c_269_, 1);
lean_inc_ref(v_k_281_);
lean_dec_ref_known(v_c_269_, 2);
v_value_282_ = lean_ctor_get(v_decl_280_, 4);
lean_inc_ref(v_value_282_);
lean_dec_ref(v_decl_280_);
v___x_283_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_268_, v_value_282_, v___y_270_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_dec_ref_known(v___x_283_, 1);
v_c_269_ = v_k_281_;
goto _start;
}
else
{
lean_dec_ref(v_k_281_);
return v___x_283_;
}
}
case 2:
{
lean_object* v_decl_285_; lean_object* v_k_286_; lean_object* v_value_287_; lean_object* v___x_288_; 
lean_del_object(v___x_276_);
v_decl_285_ = lean_ctor_get(v_c_269_, 0);
lean_inc_ref(v_decl_285_);
v_k_286_ = lean_ctor_get(v_c_269_, 1);
lean_inc_ref(v_k_286_);
lean_dec_ref_known(v_c_269_, 2);
v_value_287_ = lean_ctor_get(v_decl_285_, 4);
lean_inc_ref(v_value_287_);
lean_dec_ref(v_decl_285_);
v___x_288_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_268_, v_value_287_, v___y_270_, v___y_271_, v___y_272_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_dec_ref_known(v___x_288_, 1);
v_c_269_ = v_k_286_;
goto _start;
}
else
{
lean_dec_ref(v_k_286_);
return v___x_288_;
}
}
case 4:
{
lean_object* v_cases_290_; lean_object* v_alts_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_cases_290_ = lean_ctor_get(v_c_269_, 0);
lean_inc_ref(v_cases_290_);
lean_dec_ref_known(v_c_269_, 1);
v_alts_291_ = lean_ctor_get(v_cases_290_, 3);
lean_inc_ref(v_alts_291_);
lean_dec_ref(v_cases_290_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_array_get_size(v_alts_291_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
if (v___x_295_ == 0)
{
lean_object* v___x_297_; 
lean_dec_ref(v_alts_291_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_294_);
v___x_297_ = v___x_276_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_294_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
else
{
size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
lean_del_object(v___x_276_);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_of_nat(v___x_293_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_268_, v_alts_291_, v___x_299_, v___x_300_, v___x_294_, v___y_270_, v___y_271_, v___y_272_);
lean_dec_ref(v_alts_291_);
return v___x_301_;
}
}
case 7:
{
lean_object* v_k_302_; 
lean_del_object(v___x_276_);
v_k_302_ = lean_ctor_get(v_c_269_, 3);
lean_inc_ref(v_k_302_);
lean_dec_ref_known(v_c_269_, 4);
v_c_269_ = v_k_302_;
goto _start;
}
case 8:
{
lean_object* v_k_304_; 
lean_del_object(v___x_276_);
v_k_304_ = lean_ctor_get(v_c_269_, 3);
lean_inc_ref(v_k_304_);
lean_dec_ref_known(v_c_269_, 4);
v_c_269_ = v_k_304_;
goto _start;
}
case 9:
{
lean_object* v_k_306_; 
lean_del_object(v___x_276_);
v_k_306_ = lean_ctor_get(v_c_269_, 5);
lean_inc_ref(v_k_306_);
lean_dec_ref_known(v_c_269_, 6);
v_c_269_ = v_k_306_;
goto _start;
}
case 10:
{
lean_object* v_k_308_; 
lean_del_object(v___x_276_);
v_k_308_ = lean_ctor_get(v_c_269_, 2);
lean_inc_ref(v_k_308_);
lean_dec_ref_known(v_c_269_, 3);
v_c_269_ = v_k_308_;
goto _start;
}
case 11:
{
lean_object* v_k_310_; 
lean_del_object(v___x_276_);
v_k_310_ = lean_ctor_get(v_c_269_, 2);
lean_inc_ref(v_k_310_);
lean_dec_ref_known(v_c_269_, 3);
v_c_269_ = v_k_310_;
goto _start;
}
case 12:
{
lean_object* v_k_312_; 
lean_del_object(v___x_276_);
v_k_312_ = lean_ctor_get(v_c_269_, 3);
lean_inc_ref(v_k_312_);
lean_dec_ref_known(v_c_269_, 4);
v_c_269_ = v_k_312_;
goto _start;
}
case 13:
{
lean_object* v_k_314_; 
lean_del_object(v___x_276_);
v_k_314_ = lean_ctor_get(v_c_269_, 1);
lean_inc_ref(v_k_314_);
lean_dec_ref_known(v_c_269_, 2);
v_c_269_ = v_k_314_;
goto _start;
}
default: 
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec_ref(v_c_269_);
v___x_316_ = lean_box(0);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_316_);
v___x_318_ = v___x_276_;
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
}
else
{
lean_dec_ref(v_c_269_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(uint8_t v___x_322_, lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v___x_322_, v_x_323_, v___y_324_, v___y_325_, v___y_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go___boxed(lean_object* v_names_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_names_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_names_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1___boxed(lean_object* v_pu_335_, lean_object* v_as_336_, lean_object* v_i_337_, lean_object* v_stop_338_, lean_object* v_b_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
uint8_t v_pu_boxed_344_; size_t v_i_boxed_345_; size_t v_stop_boxed_346_; lean_object* v_res_347_; 
v_pu_boxed_344_ = lean_unbox(v_pu_335_);
v_i_boxed_345_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_stop_boxed_346_ = lean_unbox_usize(v_stop_338_);
lean_dec(v_stop_338_);
v_res_347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_boxed_344_, v_as_336_, v_i_boxed_345_, v_stop_boxed_346_, v_b_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v_as_336_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode___boxed(lean_object* v_code_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_code_348_, v_a_349_, v_a_350_, v_a_351_);
lean_dec(v_a_351_);
lean_dec_ref(v_a_350_);
lean_dec(v_a_349_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0___boxed(lean_object* v_pu_354_, lean_object* v_c_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
uint8_t v_pu_boxed_360_; lean_object* v_res_361_; 
v_pu_boxed_360_ = lean_unbox(v_pu_354_);
v_res_361_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_boxed_360_, v_c_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___boxed(lean_object* v_as_362_, lean_object* v_i_363_, lean_object* v_stop_364_, lean_object* v_b_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
size_t v_i_boxed_370_; size_t v_stop_boxed_371_; lean_object* v_res_372_; 
v_i_boxed_370_ = lean_unbox_usize(v_i_363_);
lean_dec(v_i_363_);
v_stop_boxed_371_ = lean_unbox_usize(v_stop_364_);
lean_dec(v_stop_364_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_as_362_, v_i_boxed_370_, v_stop_boxed_371_, v_b_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v_as_362_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(uint8_t v_pu_373_, lean_object* v_f_374_, lean_object* v_v_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_374_, v_v_375_, v___y_376_, v___y_377_, v___y_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___boxed(lean_object* v_pu_381_, lean_object* v_f_382_, lean_object* v_v_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
uint8_t v_pu_boxed_388_; lean_object* v_res_389_; 
v_pu_boxed_388_ = lean_unbox(v_pu_381_);
v_res_389_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(v_pu_boxed_388_, v_f_382_, v_v_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
return v_res_389_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((lean_object*)(l_Lean_Compiler_LCNF_collectUsedDecls___closed__0));
v___x_393_ = l_Lean_NameSet_empty;
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_392_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedDecls(lean_object* v_decls_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = lean_obj_once(&l_Lean_Compiler_LCNF_collectUsedDecls___closed__1, &l_Lean_Compiler_LCNF_collectUsedDecls___closed__1_once, _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1);
v___x_400_ = lean_st_mk_ref(v___x_399_);
v___x_401_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_decls_395_, v___x_400_, v_a_396_, v_a_397_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_412_; 
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_401_, 0);
lean_dec(v_unused_413_);
v___x_403_ = v___x_401_;
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
else
{
lean_dec(v___x_401_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_412_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v_localDecls_406_; lean_object* v_extSigs_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_405_ = lean_st_ref_get(v___x_400_);
lean_dec(v___x_400_);
v_localDecls_406_ = lean_ctor_get(v___x_405_, 1);
lean_inc_ref(v_localDecls_406_);
v_extSigs_407_ = lean_ctor_get(v___x_405_, 2);
lean_inc_ref(v_extSigs_407_);
lean_dec(v___x_405_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_localDecls_406_);
lean_ctor_set(v___x_408_, 1, v_extSigs_407_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_408_);
v___x_410_ = v___x_403_;
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
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v___x_400_);
v_a_414_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_401_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_401_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedDecls___boxed(lean_object* v_decls_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Compiler_LCNF_collectUsedDecls(v_decls_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec_ref(v_decls_422_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(lean_object* v_modulePrefix_427_, lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_){
_start:
{
uint8_t v___x_435_; 
v___x_435_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v_toImport_437_; uint8_t v_irPhases_438_; uint8_t v___x_439_; uint8_t v___x_440_; 
v___x_436_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
v_toImport_437_ = lean_ctor_get(v___x_436_, 0);
v_irPhases_438_ = lean_ctor_get_uint8(v___x_436_, sizeof(void*)*1);
v___x_439_ = 1;
v___x_440_ = l_Lean_instBEqIRPhases_beq(v_irPhases_438_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v_module_441_; uint8_t v___x_442_; 
v_module_441_ = lean_ctor_get(v_toImport_437_, 0);
v___x_442_ = l_Lean_Name_isPrefixOf(v_modulePrefix_427_, v_module_441_);
if (v___x_442_ == 0)
{
goto v___jp_431_;
}
else
{
return v___x_442_;
}
}
else
{
goto v___jp_431_;
}
}
else
{
uint8_t v___x_443_; 
v___x_443_ = 0;
return v___x_443_;
}
v___jp_431_:
{
size_t v___x_432_; size_t v___x_433_; 
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_add(v_i_429_, v___x_432_);
v_i_429_ = v___x_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0___boxed(lean_object* v_modulePrefix_444_, lean_object* v_as_445_, lean_object* v_i_446_, lean_object* v_stop_447_){
_start:
{
size_t v_i_boxed_448_; size_t v_stop_boxed_449_; uint8_t v_res_450_; lean_object* v_r_451_; 
v_i_boxed_448_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_stop_boxed_449_ = lean_unbox_usize(v_stop_447_);
lean_dec(v_stop_447_);
v_res_450_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_444_, v_as_445_, v_i_boxed_448_, v_stop_boxed_449_);
lean_dec_ref(v_as_445_);
lean_dec(v_modulePrefix_444_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_usesModuleFrom(lean_object* v_env_452_, lean_object* v_modulePrefix_453_){
_start:
{
lean_object* v___x_454_; lean_object* v_modules_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_454_ = l_Lean_Environment_header(v_env_452_);
v_modules_455_ = lean_ctor_get(v___x_454_, 3);
lean_inc_ref(v_modules_455_);
lean_dec_ref(v___x_454_);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_array_get_size(v_modules_455_);
v___x_458_ = lean_nat_dec_lt(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec_ref(v_modules_455_);
return v___x_458_;
}
else
{
if (v___x_458_ == 0)
{
lean_dec_ref(v_modules_455_);
return v___x_458_;
}
else
{
size_t v___x_459_; size_t v___x_460_; uint8_t v___x_461_; 
v___x_459_ = ((size_t)0ULL);
v___x_460_ = lean_usize_of_nat(v___x_457_);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_453_, v_modules_455_, v___x_459_, v___x_460_);
lean_dec_ref(v_modules_455_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_usesModuleFrom___boxed(lean_object* v_env_462_, lean_object* v_modulePrefix_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l_Lean_Compiler_LCNF_usesModuleFrom(v_env_462_, v_modulePrefix_463_);
lean_dec(v_modulePrefix_463_);
lean_dec_ref(v_env_462_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_EmitUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_EmitUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_EmitUtil(builtin);
}
#ifdef __cplusplus
}
#endif
