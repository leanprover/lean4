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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_getInitFnNameFor_x3f(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(lean_object* v_msg_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_5320__overap_37_; lean_object* v___x_38_; 
v___x_34_ = l_StateRefT_x27_instMonad___redArg(v___x_33_);
v___x_35_ = lean_box(0);
v___x_36_ = l_instInhabitedOfMonad___redArg(v___x_34_, v___x_35_);
v___x_5320__overap_37_ = lean_panic_fn_borrowed(v___x_36_, v_msg_4_);
lean_dec(v___x_36_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
v___x_38_ = lean_apply_4(v___x_5320__overap_37_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_38_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4_ = stack[0].m_obj;
lean_object* v___y_5_ = stack[1].m_obj;
lean_object* v___y_6_ = stack[2].m_obj;
lean_object* v___y_7_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v_msg_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2___boxed(lean_object* v_msg_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v_msg_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
return v_res_51_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(lean_object* v_f_52_, lean_object* v_v_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
if (lean_obj_tag(v_v_53_) == 0)
{
lean_object* v_code_58_; lean_object* v___x_59_; 
v_code_58_ = lean_ctor_get(v_v_53_, 0);
lean_inc_ref(v_code_58_);
lean_dec_ref_known(v_v_53_, 1);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
v___x_59_ = lean_apply_5(v_f_52_, v_code_58_, v___y_54_, v___y_55_, v___y_56_, lean_box(0));
return v___x_59_;
}
else
{
lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_67_; 
lean_dec_ref(v_f_52_);
v_isSharedCheck_67_ = !lean_is_exclusive(v_v_53_);
if (v_isSharedCheck_67_ == 0)
{
lean_object* v_unused_68_; 
v_unused_68_ = lean_ctor_get(v_v_53_, 0);
lean_dec(v_unused_68_);
v___x_61_ = v_v_53_;
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
else
{
lean_dec(v_v_53_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_box(0);
if (v_isShared_62_ == 0)
{
lean_ctor_set_tag(v___x_61_, 0);
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_65_ = v___x_61_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_52_ = stack[0].m_obj;
lean_object* v_v_53_ = stack[1].m_obj;
lean_object* v___y_54_ = stack[2].m_obj;
lean_object* v___y_55_ = stack[3].m_obj;
lean_object* v___y_56_ = stack[4].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_52_, v_v_53_, v___y_54_, v___y_55_, v___y_56_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg___boxed(lean_object* v_f_70_, lean_object* v_v_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_70_, v_v_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed(lean_object* v___x_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v___x_6201__boxed_83_; lean_object* v_res_84_; 
v___x_6201__boxed_83_ = lean_unbox(v___x_77_);
v_res_84_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(v___x_6201__boxed_83_, v_x_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
return v_res_84_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(lean_object* v_as_89_, size_t v_i_90_, size_t v_stop_91_, lean_object* v_b_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_a_98_; lean_object* v___y_103_; uint8_t v___x_105_; 
v___x_105_ = lean_usize_dec_eq(v_i_90_, v_stop_91_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_visited_108_; uint8_t v___x_109_; 
v___x_106_ = lean_array_uget_borrowed(v_as_89_, v_i_90_);
v___x_107_ = lean_st_ref_get(v___y_93_);
v_visited_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_visited_108_);
lean_dec(v___x_107_);
v___x_109_ = l_Lean_NameSet_contains(v_visited_108_, v___x_106_);
lean_dec(v_visited_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v_visited_111_; lean_object* v_localDecls_112_; lean_object* v_extSigs_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_202_; 
v___x_110_ = lean_st_ref_take(v___y_93_);
v_visited_111_ = lean_ctor_get(v___x_110_, 0);
v_localDecls_112_ = lean_ctor_get(v___x_110_, 1);
v_extSigs_113_ = lean_ctor_get(v___x_110_, 2);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_202_ == 0)
{
v___x_115_ = v___x_110_;
v_isShared_116_ = v_isSharedCheck_202_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_extSigs_113_);
lean_inc(v_localDecls_112_);
lean_inc(v_visited_111_);
lean_dec(v___x_110_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_202_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
lean_inc(v___x_106_);
v___x_117_ = l_Lean_NameSet_insert(v_visited_111_, v___x_106_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_117_);
v___x_119_ = v___x_115_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_117_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_localDecls_112_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_extSigs_113_);
v___x_119_ = v_reuseFailAlloc_201_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_st_ref_put(v___y_93_, v___x_119_);
v___x_121_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v___x_106_, v___y_95_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v___x_121_, 1);
if (lean_obj_tag(v_a_122_) == 1)
{
lean_object* v_val_123_; lean_object* v___x_124_; lean_object* v_visited_125_; lean_object* v_localDecls_126_; lean_object* v_extSigs_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_155_; 
v_val_123_ = lean_ctor_get(v_a_122_, 0);
lean_inc(v_val_123_);
lean_dec_ref_known(v_a_122_, 1);
v___x_124_ = lean_st_ref_take(v___y_93_);
v_visited_125_ = lean_ctor_get(v___x_124_, 0);
v_localDecls_126_ = lean_ctor_get(v___x_124_, 1);
v_extSigs_127_ = lean_ctor_get(v___x_124_, 2);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_155_ == 0)
{
v___x_129_ = v___x_124_;
v_isShared_130_ = v_isSharedCheck_155_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_extSigs_127_);
lean_inc(v_localDecls_126_);
lean_inc(v_visited_125_);
lean_dec(v___x_124_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_155_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
lean_inc(v_val_123_);
v___x_131_ = lean_array_push(v_localDecls_126_, v_val_123_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_131_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_visited_125_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_154_, 2, v_extSigs_127_);
v___x_133_ = v_reuseFailAlloc_154_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; lean_object* v_toSignature_135_; lean_object* v_value_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___f_139_; lean_object* v___x_140_; 
v___x_134_ = lean_st_ref_put(v___y_93_, v___x_133_);
v_toSignature_135_ = lean_ctor_get(v_val_123_, 0);
lean_inc_ref(v_toSignature_135_);
v_value_136_ = lean_ctor_get(v_val_123_, 1);
lean_inc_ref(v_value_136_);
lean_dec(v_val_123_);
v___x_137_ = 1;
v___x_138_ = lean_box(v___x_137_);
v___f_139_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0___boxed), 6, 1);
lean_closure_set(v___f_139_, 0, v___x_138_);
v___x_140_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v___f_139_, v_value_136_, v___y_93_, v___y_94_, v___y_95_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v___x_141_; lean_object* v___y_143_; lean_object* v_env_150_; lean_object* v_name_151_; lean_object* v___x_152_; 
lean_dec_ref_known(v___x_140_, 1);
v___x_141_ = lean_st_ref_get(v___y_95_);
v_env_150_ = lean_ctor_get(v___x_141_, 0);
lean_inc_ref_n(v_env_150_, 2);
lean_dec(v___x_141_);
v_name_151_ = lean_ctor_get(v_toSignature_135_, 0);
lean_inc_n(v_name_151_, 2);
lean_dec_ref(v_toSignature_135_);
v___x_152_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_150_, v_name_151_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_getInitFnNameFor_x3f(v_env_150_, v_name_151_);
v___y_143_ = v___x_153_;
goto v___jp_142_;
}
else
{
lean_dec(v_name_151_);
lean_dec_ref(v_env_150_);
v___y_143_ = v___x_152_;
goto v___jp_142_;
}
v___jp_142_:
{
if (lean_obj_tag(v___y_143_) == 1)
{
lean_object* v_val_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_val_144_ = lean_ctor_get(v___y_143_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___y_143_, 1);
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
v___x_147_ = lean_array_push(v___x_146_, v_val_144_);
v___x_148_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_147_, v___y_93_, v___y_94_, v___y_95_);
lean_dec_ref(v___x_147_);
v___y_103_ = v___x_148_;
goto v___jp_102_;
}
else
{
lean_object* v___x_149_; 
lean_dec(v___y_143_);
v___x_149_ = lean_box(0);
v_a_98_ = v___x_149_;
goto v___jp_97_;
}
}
}
else
{
lean_dec_ref(v_toSignature_135_);
v___y_103_ = v___x_140_;
goto v___jp_102_;
}
}
}
}
else
{
lean_object* v___x_156_; 
lean_dec(v_a_122_);
lean_inc(v___x_106_);
v___x_156_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v___x_106_, v___y_95_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
if (lean_obj_tag(v_a_157_) == 1)
{
lean_object* v_val_158_; lean_object* v___x_159_; lean_object* v_visited_160_; lean_object* v_localDecls_161_; lean_object* v_extSigs_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_172_; 
v_val_158_ = lean_ctor_get(v_a_157_, 0);
lean_inc(v_val_158_);
lean_dec_ref_known(v_a_157_, 1);
v___x_159_ = lean_st_ref_take(v___y_93_);
v_visited_160_ = lean_ctor_get(v___x_159_, 0);
v_localDecls_161_ = lean_ctor_get(v___x_159_, 1);
v_extSigs_162_ = lean_ctor_get(v___x_159_, 2);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_172_ == 0)
{
v___x_164_ = v___x_159_;
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_extSigs_162_);
lean_inc(v_localDecls_161_);
lean_inc(v_visited_160_);
lean_dec(v___x_159_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_array_push(v_extSigs_162_, v_val_158_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 2, v___x_167_);
v___x_169_ = v___x_164_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_visited_160_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_localDecls_161_);
lean_ctor_set(v_reuseFailAlloc_171_, 2, v___x_167_);
v___x_169_ = v_reuseFailAlloc_171_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = lean_st_ref_put(v___y_93_, v___x_169_);
v_a_98_ = v___x_166_;
goto v___jp_97_;
}
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_a_157_);
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0));
v___x_174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1));
v___x_175_ = lean_unsigned_to_nat(42u);
v___x_176_ = lean_unsigned_to_nat(8u);
v___x_177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2));
v___x_178_ = 1;
lean_inc(v___x_106_);
v___x_179_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_106_, v___x_178_);
v___x_180_ = lean_string_append(v___x_177_, v___x_179_);
lean_dec_ref(v___x_179_);
v___x_181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3));
v___x_182_ = lean_string_append(v___x_180_, v___x_181_);
v___x_183_ = l_mkPanicMessageWithDecl(v___x_173_, v___x_174_, v___x_175_, v___x_176_, v___x_182_);
lean_dec_ref(v___x_182_);
v___x_184_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v___x_183_, v___y_93_, v___y_94_, v___y_95_);
v___y_103_ = v___x_184_;
goto v___jp_102_;
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
v_a_185_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_156_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_156_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
v_a_193_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_121_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_121_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
}
else
{
lean_object* v___x_203_; 
v___x_203_ = lean_box(0);
v_a_98_ = v___x_203_;
goto v___jp_97_;
}
}
else
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v_b_92_);
return v___x_204_;
}
v___jp_97_:
{
size_t v___x_99_; size_t v___x_100_; 
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_add(v_i_90_, v___x_99_);
v_i_90_ = v___x_100_;
v_b_92_ = v_a_98_;
goto _start;
}
v___jp_102_:
{
if (lean_obj_tag(v___y_103_) == 0)
{
lean_object* v_a_104_; 
v_a_104_ = lean_ctor_get(v___y_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___y_103_, 1);
v_a_98_ = v_a_104_;
goto v___jp_97_;
}
else
{
return v___y_103_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_89_ = stack[0].m_obj;
size_t v_i_90_ = stack[1].m_num;
size_t v_stop_91_ = stack[2].m_num;
lean_object* v_b_92_ = stack[3].m_obj;
lean_object* v___y_93_ = stack[4].m_obj;
lean_object* v___y_94_ = stack[5].m_obj;
lean_object* v___y_95_ = stack[6].m_obj;
lean_object* v_res_205_;
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_as_89_, v_i_90_, v_stop_91_, v_b_92_, v___y_93_, v___y_94_, v___y_95_);
stack->m_obj
 = v_res_205_;
}
lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(lean_object* v_names_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_array_get_size(v_names_206_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_nat_dec_lt(v___x_211_, v___x_212_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_213_);
return v___x_215_;
}
else
{
uint8_t v___x_216_; 
v___x_216_ = lean_nat_dec_le(v___x_212_, v___x_212_);
if (v___x_216_ == 0)
{
if (v___x_214_ == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_217_, 0, v___x_213_);
return v___x_217_;
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_212_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_206_, v___x_218_, v___x_219_, v___x_213_, v_a_207_, v_a_208_, v_a_209_);
return v___x_220_;
}
}
else
{
size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_212_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_206_, v___x_221_, v___x_222_, v___x_213_, v_a_207_, v_a_208_, v_a_209_);
return v___x_223_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_names_206_ = stack[0].m_obj;
lean_object* v_a_207_ = stack[1].m_obj;
lean_object* v_a_208_ = stack[2].m_obj;
lean_object* v_a_209_ = stack[3].m_obj;
lean_object* v_res_224_;
v_res_224_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_names_206_, v_a_207_, v_a_208_, v_a_209_);
stack->m_obj
 = v_res_224_;
}
lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(lean_object* v_code_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_declName_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; 
if (lean_obj_tag(v_code_225_) == 0)
{
lean_object* v_decl_239_; lean_object* v_value_240_; 
v_decl_239_ = lean_ctor_get(v_code_225_, 0);
lean_inc_ref(v_decl_239_);
lean_dec_ref_known(v_code_225_, 2);
v_value_240_ = lean_ctor_get(v_decl_239_, 3);
lean_inc(v_value_240_);
lean_dec_ref(v_decl_239_);
switch(lean_obj_tag(v_value_240_))
{
case 3:
{
lean_object* v_declName_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_declName_241_ = lean_ctor_get(v_value_240_, 0);
lean_inc(v_declName_241_);
lean_dec_ref_known(v_value_240_, 3);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_mk_empty_array_with_capacity(v___x_242_);
v___x_244_ = lean_array_push(v___x_243_, v_declName_241_);
v___x_245_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_244_, v_a_226_, v_a_227_, v_a_228_);
lean_dec_ref(v___x_244_);
return v___x_245_;
}
case 9:
{
lean_object* v_fn_246_; 
v_fn_246_ = lean_ctor_get(v_value_240_, 0);
lean_inc(v_fn_246_);
lean_dec_ref_known(v_value_240_, 2);
v_declName_231_ = v_fn_246_;
v___y_232_ = v_a_226_;
v___y_233_ = v_a_227_;
v___y_234_ = v_a_228_;
goto v___jp_230_;
}
case 10:
{
lean_object* v_fn_247_; 
v_fn_247_ = lean_ctor_get(v_value_240_, 0);
lean_inc(v_fn_247_);
lean_dec_ref_known(v_value_240_, 2);
v_declName_231_ = v_fn_247_;
v___y_232_ = v_a_226_;
v___y_233_ = v_a_227_;
v___y_234_ = v_a_228_;
goto v___jp_230_;
}
default: 
{
lean_object* v___x_248_; lean_object* v___x_249_; 
lean_dec(v_value_240_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v_code_225_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
v___jp_230_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_mk_empty_array_with_capacity(v___x_235_);
v___x_237_ = lean_array_push(v___x_236_, v_declName_231_);
v___x_238_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_237_, v___y_232_, v___y_233_, v___y_234_);
lean_dec_ref(v___x_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_225_ = stack[0].m_obj;
lean_object* v_a_226_ = stack[1].m_obj;
lean_object* v_a_227_ = stack[2].m_obj;
lean_object* v_a_228_ = stack[3].m_obj;
lean_object* v_res_252_;
v_res_252_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_code_225_, v_a_226_, v_a_227_, v_a_228_);
stack->m_obj
 = v_res_252_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(uint8_t v_pu_253_, lean_object* v_as_254_, size_t v_i_255_, size_t v_stop_256_, lean_object* v_b_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___y_263_; uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_eq(v_i_255_, v_stop_256_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_array_uget_borrowed(v_as_254_, v_i_255_);
switch(lean_obj_tag(v___x_269_))
{
case 0:
{
lean_object* v_code_270_; lean_object* v___x_271_; 
v_code_270_ = lean_ctor_get(v___x_269_, 2);
lean_inc_ref(v_code_270_);
v___x_271_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_253_, v_code_270_, v___y_258_, v___y_259_, v___y_260_);
v___y_263_ = v___x_271_;
goto v___jp_262_;
}
case 1:
{
lean_object* v_code_272_; lean_object* v___x_273_; 
v_code_272_ = lean_ctor_get(v___x_269_, 1);
lean_inc_ref(v_code_272_);
v___x_273_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_253_, v_code_272_, v___y_258_, v___y_259_, v___y_260_);
v___y_263_ = v___x_273_;
goto v___jp_262_;
}
default: 
{
lean_object* v_code_274_; lean_object* v___x_275_; 
v_code_274_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_code_274_);
v___x_275_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_253_, v_code_274_, v___y_258_, v___y_259_, v___y_260_);
v___y_263_ = v___x_275_;
goto v___jp_262_;
}
}
}
else
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_b_257_);
return v___x_276_;
}
v___jp_262_:
{
if (lean_obj_tag(v___y_263_) == 0)
{
lean_object* v_a_264_; size_t v___x_265_; size_t v___x_266_; 
v_a_264_ = lean_ctor_get(v___y_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___y_263_, 1);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_add(v_i_255_, v___x_265_);
v_i_255_ = v___x_266_;
v_b_257_ = v_a_264_;
goto _start;
}
else
{
return v___y_263_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_253_ = stack[0].m_num;
lean_object* v_as_254_ = stack[1].m_obj;
size_t v_i_255_ = stack[2].m_num;
size_t v_stop_256_ = stack[3].m_num;
lean_object* v_b_257_ = stack[4].m_obj;
lean_object* v___y_258_ = stack[5].m_obj;
lean_object* v___y_259_ = stack[6].m_obj;
lean_object* v___y_260_ = stack[7].m_obj;
lean_object* v_res_277_;
v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_253_, v_as_254_, v_i_255_, v_stop_256_, v_b_257_, v___y_258_, v___y_259_, v___y_260_);
stack->m_obj
 = v_res_277_;
}
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(uint8_t v_pu_278_, lean_object* v_c_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
lean_inc_ref(v_c_279_);
v___x_284_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_c_279_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_330_; 
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; 
v_unused_331_ = lean_ctor_get(v___x_284_, 0);
lean_dec(v_unused_331_);
v___x_286_ = v___x_284_;
v_isShared_287_ = v_isSharedCheck_330_;
goto v_resetjp_285_;
}
else
{
lean_dec(v___x_284_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_330_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
switch(lean_obj_tag(v_c_279_))
{
case 0:
{
lean_object* v_k_288_; 
lean_del_object(v___x_286_);
v_k_288_ = lean_ctor_get(v_c_279_, 1);
lean_inc_ref(v_k_288_);
lean_dec_ref_known(v_c_279_, 2);
v_c_279_ = v_k_288_;
goto _start;
}
case 1:
{
lean_object* v_decl_290_; lean_object* v_k_291_; lean_object* v_value_292_; lean_object* v___x_293_; 
lean_del_object(v___x_286_);
v_decl_290_ = lean_ctor_get(v_c_279_, 0);
lean_inc_ref(v_decl_290_);
v_k_291_ = lean_ctor_get(v_c_279_, 1);
lean_inc_ref(v_k_291_);
lean_dec_ref_known(v_c_279_, 2);
v_value_292_ = lean_ctor_get(v_decl_290_, 4);
lean_inc_ref(v_value_292_);
lean_dec_ref(v_decl_290_);
v___x_293_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_278_, v_value_292_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_dec_ref_known(v___x_293_, 1);
v_c_279_ = v_k_291_;
goto _start;
}
else
{
lean_dec_ref(v_k_291_);
return v___x_293_;
}
}
case 2:
{
lean_object* v_decl_295_; lean_object* v_k_296_; lean_object* v_value_297_; lean_object* v___x_298_; 
lean_del_object(v___x_286_);
v_decl_295_ = lean_ctor_get(v_c_279_, 0);
lean_inc_ref(v_decl_295_);
v_k_296_ = lean_ctor_get(v_c_279_, 1);
lean_inc_ref(v_k_296_);
lean_dec_ref_known(v_c_279_, 2);
v_value_297_ = lean_ctor_get(v_decl_295_, 4);
lean_inc_ref(v_value_297_);
lean_dec_ref(v_decl_295_);
v___x_298_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_278_, v_value_297_, v___y_280_, v___y_281_, v___y_282_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_dec_ref_known(v___x_298_, 1);
v_c_279_ = v_k_296_;
goto _start;
}
else
{
lean_dec_ref(v_k_296_);
return v___x_298_;
}
}
case 4:
{
lean_object* v_cases_300_; lean_object* v_alts_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_cases_300_ = lean_ctor_get(v_c_279_, 0);
lean_inc_ref(v_cases_300_);
lean_dec_ref_known(v_c_279_, 1);
v_alts_301_ = lean_ctor_get(v_cases_300_, 3);
lean_inc_ref(v_alts_301_);
lean_dec_ref(v_cases_300_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_array_get_size(v_alts_301_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_nat_dec_lt(v___x_302_, v___x_303_);
if (v___x_305_ == 0)
{
lean_object* v___x_307_; 
lean_dec_ref(v_alts_301_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_304_);
v___x_307_ = v___x_286_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_304_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
else
{
size_t v___x_309_; size_t v___x_310_; lean_object* v___x_311_; 
lean_del_object(v___x_286_);
v___x_309_ = ((size_t)0ULL);
v___x_310_ = lean_usize_of_nat(v___x_303_);
v___x_311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_278_, v_alts_301_, v___x_309_, v___x_310_, v___x_304_, v___y_280_, v___y_281_, v___y_282_);
lean_dec_ref(v_alts_301_);
return v___x_311_;
}
}
case 7:
{
lean_object* v_k_312_; 
lean_del_object(v___x_286_);
v_k_312_ = lean_ctor_get(v_c_279_, 3);
lean_inc_ref(v_k_312_);
lean_dec_ref_known(v_c_279_, 4);
v_c_279_ = v_k_312_;
goto _start;
}
case 8:
{
lean_object* v_k_314_; 
lean_del_object(v___x_286_);
v_k_314_ = lean_ctor_get(v_c_279_, 3);
lean_inc_ref(v_k_314_);
lean_dec_ref_known(v_c_279_, 4);
v_c_279_ = v_k_314_;
goto _start;
}
case 9:
{
lean_object* v_k_316_; 
lean_del_object(v___x_286_);
v_k_316_ = lean_ctor_get(v_c_279_, 5);
lean_inc_ref(v_k_316_);
lean_dec_ref_known(v_c_279_, 6);
v_c_279_ = v_k_316_;
goto _start;
}
case 10:
{
lean_object* v_k_318_; 
lean_del_object(v___x_286_);
v_k_318_ = lean_ctor_get(v_c_279_, 2);
lean_inc_ref(v_k_318_);
lean_dec_ref_known(v_c_279_, 3);
v_c_279_ = v_k_318_;
goto _start;
}
case 11:
{
lean_object* v_k_320_; 
lean_del_object(v___x_286_);
v_k_320_ = lean_ctor_get(v_c_279_, 2);
lean_inc_ref(v_k_320_);
lean_dec_ref_known(v_c_279_, 3);
v_c_279_ = v_k_320_;
goto _start;
}
case 12:
{
lean_object* v_k_322_; 
lean_del_object(v___x_286_);
v_k_322_ = lean_ctor_get(v_c_279_, 3);
lean_inc_ref(v_k_322_);
lean_dec_ref_known(v_c_279_, 4);
v_c_279_ = v_k_322_;
goto _start;
}
case 13:
{
lean_object* v_k_324_; 
lean_del_object(v___x_286_);
v_k_324_ = lean_ctor_get(v_c_279_, 1);
lean_inc_ref(v_k_324_);
lean_dec_ref_known(v_c_279_, 2);
v_c_279_ = v_k_324_;
goto _start;
}
default: 
{
lean_object* v___x_326_; lean_object* v___x_328_; 
lean_dec_ref(v_c_279_);
v___x_326_ = lean_box(0);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_326_);
v___x_328_ = v___x_286_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
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
}
else
{
lean_dec_ref(v_c_279_);
return v___x_284_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_278_ = stack[0].m_num;
lean_object* v_c_279_ = stack[1].m_obj;
lean_object* v___y_280_ = stack[2].m_obj;
lean_object* v___y_281_ = stack[3].m_obj;
lean_object* v___y_282_ = stack[4].m_obj;
lean_object* v_res_332_;
v_res_332_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_278_, v_c_279_, v___y_280_, v___y_281_, v___y_282_);
stack->m_obj
 = v_res_332_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(uint8_t v___x_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v___x_333_, v_x_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_339_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_333_ = stack[0].m_num;
lean_object* v_x_334_ = stack[1].m_obj;
lean_object* v___y_335_ = stack[2].m_obj;
lean_object* v___y_336_ = stack[3].m_obj;
lean_object* v___y_337_ = stack[4].m_obj;
lean_object* v_res_340_;
v_res_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(v___x_333_, v_x_334_, v___y_335_, v___y_336_, v___y_337_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1___boxed(lean_object* v_pu_341_, lean_object* v_as_342_, lean_object* v_i_343_, lean_object* v_stop_344_, lean_object* v_b_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
uint8_t v_pu_boxed_350_; size_t v_i_boxed_351_; size_t v_stop_boxed_352_; lean_object* v_res_353_; 
v_pu_boxed_350_ = lean_unbox(v_pu_341_);
v_i_boxed_351_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_stop_boxed_352_ = lean_unbox_usize(v_stop_344_);
lean_dec(v_stop_344_);
v_res_353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_boxed_350_, v_as_342_, v_i_boxed_351_, v_stop_boxed_352_, v_b_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v_as_342_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go___boxed(lean_object* v_names_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_names_354_, v_a_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
lean_dec(v_a_355_);
lean_dec_ref(v_names_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode___boxed(lean_object* v_code_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_code_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_a_361_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0___boxed(lean_object* v_pu_366_, lean_object* v_c_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v_pu_boxed_372_; lean_object* v_res_373_; 
v_pu_boxed_372_ = lean_unbox(v_pu_366_);
v_res_373_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_boxed_372_, v_c_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___boxed(lean_object* v_as_374_, lean_object* v_i_375_, lean_object* v_stop_376_, lean_object* v_b_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
size_t v_i_boxed_382_; size_t v_stop_boxed_383_; lean_object* v_res_384_; 
v_i_boxed_382_ = lean_unbox_usize(v_i_375_);
lean_dec(v_i_375_);
v_stop_boxed_383_ = lean_unbox_usize(v_stop_376_);
lean_dec(v_stop_376_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_as_374_, v_i_boxed_382_, v_stop_boxed_383_, v_b_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v_as_374_);
return v_res_384_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(uint8_t v_pu_385_, lean_object* v_f_386_, lean_object* v_v_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_386_, v_v_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_392_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_385_ = stack[0].m_num;
lean_object* v_f_386_ = stack[1].m_obj;
lean_object* v_v_387_ = stack[2].m_obj;
lean_object* v___y_388_ = stack[3].m_obj;
lean_object* v___y_389_ = stack[4].m_obj;
lean_object* v___y_390_ = stack[5].m_obj;
lean_object* v_res_393_;
v_res_393_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(v_pu_385_, v_f_386_, v_v_387_, v___y_388_, v___y_389_, v___y_390_);
stack->m_obj
 = v_res_393_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___boxed(lean_object* v_pu_394_, lean_object* v_f_395_, lean_object* v_v_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
uint8_t v_pu_boxed_401_; lean_object* v_res_402_; 
v_pu_boxed_401_ = lean_unbox(v_pu_394_);
v_res_402_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(v_pu_boxed_401_, v_f_395_, v_v_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
return v_res_402_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = ((lean_object*)(l_Lean_Compiler_LCNF_collectUsedDecls___closed__0));
v___x_406_ = l_Lean_NameSet_empty;
v___x_407_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
lean_ctor_set(v___x_407_, 2, v___x_405_);
return v___x_407_;
}
}
lean_object* l_Lean_Compiler_LCNF_collectUsedDecls(lean_object* v_decls_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = lean_obj_once(&l_Lean_Compiler_LCNF_collectUsedDecls___closed__1, &l_Lean_Compiler_LCNF_collectUsedDecls___closed__1_once, _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1);
v___x_413_ = lean_st_mk_ref(v___x_412_);
v___x_414_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_decls_408_, v___x_413_, v_a_409_, v_a_410_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_425_; 
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v___x_414_, 0);
lean_dec(v_unused_426_);
v___x_416_ = v___x_414_;
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___x_414_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v_localDecls_419_; lean_object* v_extSigs_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_418_ = lean_st_ref_get(v___x_413_);
lean_dec(v___x_413_);
v_localDecls_419_ = lean_ctor_get(v___x_418_, 1);
lean_inc_ref(v_localDecls_419_);
v_extSigs_420_ = lean_ctor_get(v___x_418_, 2);
lean_inc_ref(v_extSigs_420_);
lean_dec(v___x_418_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_localDecls_419_);
lean_ctor_set(v___x_421_, 1, v_extSigs_420_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_421_);
v___x_423_ = v___x_416_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v___x_413_);
v_a_427_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_414_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_414_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_collectUsedDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_408_ = stack[0].m_obj;
lean_object* v_a_409_ = stack[1].m_obj;
lean_object* v_a_410_ = stack[2].m_obj;
lean_object* v_res_435_;
v_res_435_ = l_Lean_Compiler_LCNF_collectUsedDecls(v_decls_408_, v_a_409_, v_a_410_);
stack->m_obj
 = v_res_435_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedDecls___boxed(lean_object* v_decls_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Compiler_LCNF_collectUsedDecls(v_decls_436_, v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec_ref(v_decls_436_);
return v_res_440_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(lean_object* v_modulePrefix_441_, lean_object* v_as_442_, size_t v_i_443_, size_t v_stop_444_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_usize_dec_eq(v_i_443_, v_stop_444_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v_toImport_451_; uint8_t v_irPhases_452_; uint8_t v___x_453_; uint8_t v___x_454_; 
v___x_450_ = lean_array_uget_borrowed(v_as_442_, v_i_443_);
v_toImport_451_ = lean_ctor_get(v___x_450_, 0);
v_irPhases_452_ = lean_ctor_get_uint8(v___x_450_, sizeof(void*)*1);
v___x_453_ = 1;
v___x_454_ = l_Lean_instBEqIRPhases_beq(v_irPhases_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v_module_455_; uint8_t v___x_456_; 
v_module_455_ = lean_ctor_get(v_toImport_451_, 0);
v___x_456_ = l_Lean_Name_isPrefixOf(v_modulePrefix_441_, v_module_455_);
if (v___x_456_ == 0)
{
goto v___jp_445_;
}
else
{
return v___x_456_;
}
}
else
{
goto v___jp_445_;
}
}
else
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
v___jp_445_:
{
size_t v___x_446_; size_t v___x_447_; 
v___x_446_ = ((size_t)1ULL);
v___x_447_ = lean_usize_add(v_i_443_, v___x_446_);
v_i_443_ = v___x_447_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_modulePrefix_441_ = stack[0].m_obj;
lean_object* v_as_442_ = stack[1].m_obj;
size_t v_i_443_ = stack[2].m_num;
size_t v_stop_444_ = stack[3].m_num;
uint8_t v_res_458_;
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_441_, v_as_442_, v_i_443_, v_stop_444_);
stack->m_num = v_res_458_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0___boxed(lean_object* v_modulePrefix_459_, lean_object* v_as_460_, lean_object* v_i_461_, lean_object* v_stop_462_){
_start:
{
size_t v_i_boxed_463_; size_t v_stop_boxed_464_; uint8_t v_res_465_; lean_object* v_r_466_; 
v_i_boxed_463_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_stop_boxed_464_ = lean_unbox_usize(v_stop_462_);
lean_dec(v_stop_462_);
v_res_465_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_459_, v_as_460_, v_i_boxed_463_, v_stop_boxed_464_);
lean_dec_ref(v_as_460_);
lean_dec(v_modulePrefix_459_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
uint8_t l_Lean_Compiler_LCNF_usesModuleFrom(lean_object* v_env_467_, lean_object* v_modulePrefix_468_){
_start:
{
lean_object* v___x_469_; lean_object* v_modules_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_469_ = l_Lean_Environment_header(v_env_467_);
v_modules_470_ = lean_ctor_get(v___x_469_, 3);
lean_inc_ref(v_modules_470_);
lean_dec_ref(v___x_469_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_array_get_size(v_modules_470_);
v___x_473_ = lean_nat_dec_lt(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_dec_ref(v_modules_470_);
return v___x_473_;
}
else
{
if (v___x_473_ == 0)
{
lean_dec_ref(v_modules_470_);
return v___x_473_;
}
else
{
size_t v___x_474_; size_t v___x_475_; uint8_t v___x_476_; 
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_472_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_468_, v_modules_470_, v___x_474_, v___x_475_);
lean_dec_ref(v_modules_470_);
return v___x_476_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_usesModuleFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_467_ = stack[0].m_obj;
lean_object* v_modulePrefix_468_ = stack[1].m_obj;
uint8_t v_res_477_;
v_res_477_ = l_Lean_Compiler_LCNF_usesModuleFrom(v_env_467_, v_modulePrefix_468_);
stack->m_num = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_usesModuleFrom___boxed(lean_object* v_env_478_, lean_object* v_modulePrefix_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Lean_Compiler_LCNF_usesModuleFrom(v_env_478_, v_modulePrefix_479_);
lean_dec(v_modulePrefix_479_);
lean_dec_ref(v_env_478_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
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
