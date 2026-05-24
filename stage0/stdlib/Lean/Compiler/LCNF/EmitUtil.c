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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_getBuiltinInitFnNameFor_x3f(lean_object*, lean_object*);
lean_object* lean_get_init_fn_name_for(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
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
v___x_1_ = l_instMonadEIO(lean_box(0));
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
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_5823__overap_37_; lean_object* v___x_38_; 
v___x_34_ = l_StateRefT_x27_instMonad___redArg(v___x_33_);
v___x_35_ = lean_box(0);
v___x_36_ = l_instInhabitedOfMonad___redArg(v___x_34_, v___x_35_);
v___x_5823__overap_37_ = lean_panic_fn_borrowed(v___x_36_, v_msg_4_);
lean_dec(v___x_36_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
v___x_38_ = lean_apply_4(v___x_5823__overap_37_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
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
uint8_t v___x_6627__boxed_81_; lean_object* v_res_82_; 
v___x_6627__boxed_81_ = lean_unbox(v___x_75_);
v_res_82_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(v___x_6627__boxed_81_, v_x_76_, v___y_77_, v___y_78_, v___y_79_);
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
lean_object* v___x_104_; lean_object* v_visited_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_104_ = lean_st_ref_get(v___y_91_);
v_visited_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_visited_105_);
lean_dec(v___x_104_);
v___x_106_ = lean_array_uget_borrowed(v_as_87_, v_i_88_);
v___x_107_ = l_Lean_NameSet_contains(v_visited_105_, v___x_106_);
lean_dec(v_visited_105_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v_visited_109_; lean_object* v_localDecls_110_; lean_object* v_extSigs_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_200_; 
v___x_108_ = lean_st_ref_take(v___y_91_);
v_visited_109_ = lean_ctor_get(v___x_108_, 0);
v_localDecls_110_ = lean_ctor_get(v___x_108_, 1);
v_extSigs_111_ = lean_ctor_get(v___x_108_, 2);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_200_ == 0)
{
v___x_113_ = v___x_108_;
v_isShared_114_ = v_isSharedCheck_200_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_extSigs_111_);
lean_inc(v_localDecls_110_);
lean_inc(v_visited_109_);
lean_dec(v___x_108_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_200_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_inc(v___x_106_);
v___x_115_ = l_Lean_NameSet_insert(v_visited_109_, v___x_106_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_115_);
v___x_117_ = v___x_113_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_115_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v_localDecls_110_);
lean_ctor_set(v_reuseFailAlloc_199_, 2, v_extSigs_111_);
v___x_117_ = v_reuseFailAlloc_199_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_st_ref_set(v___y_91_, v___x_117_);
v___x_119_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v___x_106_, v___y_93_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref_known(v___x_119_, 1);
if (lean_obj_tag(v_a_120_) == 1)
{
lean_object* v_val_121_; lean_object* v___x_122_; lean_object* v_visited_123_; lean_object* v_localDecls_124_; lean_object* v_extSigs_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_153_; 
v_val_121_ = lean_ctor_get(v_a_120_, 0);
lean_inc(v_val_121_);
lean_dec_ref_known(v_a_120_, 1);
v___x_122_ = lean_st_ref_take(v___y_91_);
v_visited_123_ = lean_ctor_get(v___x_122_, 0);
v_localDecls_124_ = lean_ctor_get(v___x_122_, 1);
v_extSigs_125_ = lean_ctor_get(v___x_122_, 2);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_153_ == 0)
{
v___x_127_ = v___x_122_;
v_isShared_128_ = v_isSharedCheck_153_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_extSigs_125_);
lean_inc(v_localDecls_124_);
lean_inc(v_visited_123_);
lean_dec(v___x_122_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_153_;
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
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_visited_123_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_extSigs_125_);
v___x_131_ = v_reuseFailAlloc_152_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v_toSignature_133_; lean_object* v_value_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___f_137_; lean_object* v___x_138_; 
v___x_132_ = lean_st_ref_set(v___y_91_, v___x_131_);
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
lean_object* v___x_139_; lean_object* v___y_141_; lean_object* v_env_148_; lean_object* v_name_149_; lean_object* v___x_150_; 
lean_dec_ref_known(v___x_138_, 1);
v___x_139_ = lean_st_ref_get(v___y_93_);
v_env_148_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref_n(v_env_148_, 2);
lean_dec(v___x_139_);
v_name_149_ = lean_ctor_get(v_toSignature_133_, 0);
lean_inc_n(v_name_149_, 2);
lean_dec_ref(v_toSignature_133_);
v___x_150_ = l_Lean_getBuiltinInitFnNameFor_x3f(v_env_148_, v_name_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v___x_151_; 
v___x_151_ = lean_get_init_fn_name_for(v_env_148_, v_name_149_);
v___y_141_ = v___x_151_;
goto v___jp_140_;
}
else
{
lean_dec(v_name_149_);
lean_dec_ref(v_env_148_);
v___y_141_ = v___x_150_;
goto v___jp_140_;
}
v___jp_140_:
{
if (lean_obj_tag(v___y_141_) == 1)
{
lean_object* v_val_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_val_142_ = lean_ctor_get(v___y_141_, 0);
lean_inc(v_val_142_);
lean_dec_ref_known(v___y_141_, 1);
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_mk_empty_array_with_capacity(v___x_143_);
v___x_145_ = lean_array_push(v___x_144_, v_val_142_);
v___x_146_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_145_, v___y_91_, v___y_92_, v___y_93_);
lean_dec_ref(v___x_145_);
v___y_101_ = v___x_146_;
goto v___jp_100_;
}
else
{
lean_object* v___x_147_; 
lean_dec(v___y_141_);
v___x_147_ = lean_box(0);
v_a_96_ = v___x_147_;
goto v___jp_95_;
}
}
}
else
{
lean_dec_ref(v_toSignature_133_);
v___y_101_ = v___x_138_;
goto v___jp_100_;
}
}
}
}
else
{
lean_object* v___x_154_; 
lean_dec(v_a_120_);
lean_inc(v___x_106_);
v___x_154_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v___x_106_, v___y_93_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
if (lean_obj_tag(v_a_155_) == 1)
{
lean_object* v_val_156_; lean_object* v___x_157_; lean_object* v_visited_158_; lean_object* v_localDecls_159_; lean_object* v_extSigs_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_170_; 
v_val_156_ = lean_ctor_get(v_a_155_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v_a_155_, 1);
v___x_157_ = lean_st_ref_take(v___y_91_);
v_visited_158_ = lean_ctor_get(v___x_157_, 0);
v_localDecls_159_ = lean_ctor_get(v___x_157_, 1);
v_extSigs_160_ = lean_ctor_get(v___x_157_, 2);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_170_ == 0)
{
v___x_162_ = v___x_157_;
v_isShared_163_ = v_isSharedCheck_170_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_extSigs_160_);
lean_inc(v_localDecls_159_);
lean_inc(v_visited_158_);
lean_dec(v___x_157_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_170_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_array_push(v_extSigs_160_, v_val_156_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 2, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_visited_158_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_localDecls_159_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v___x_164_);
v___x_166_ = v_reuseFailAlloc_169_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_st_ref_set(v___y_91_, v___x_166_);
v___x_168_ = lean_box(0);
v_a_96_ = v___x_168_;
goto v___jp_95_;
}
}
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_a_155_);
v___x_171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__0));
v___x_172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__1));
v___x_173_ = lean_unsigned_to_nat(42u);
v___x_174_ = lean_unsigned_to_nat(8u);
v___x_175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__2));
v___x_176_ = 1;
lean_inc(v___x_106_);
v___x_177_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_106_, v___x_176_);
v___x_178_ = lean_string_append(v___x_175_, v___x_177_);
lean_dec_ref(v___x_177_);
v___x_179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___closed__3));
v___x_180_ = lean_string_append(v___x_178_, v___x_179_);
v___x_181_ = l_mkPanicMessageWithDecl(v___x_171_, v___x_172_, v___x_173_, v___x_174_, v___x_180_);
lean_dec_ref(v___x_180_);
v___x_182_ = l_panic___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__2(v___x_181_, v___y_91_, v___y_92_, v___y_93_);
v___y_101_ = v___x_182_;
goto v___jp_100_;
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_154_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_154_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
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
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
v_a_191_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_119_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_119_);
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
}
else
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(0);
v_a_96_ = v___x_201_;
goto v___jp_95_;
}
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v_b_90_);
return v___x_202_;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(lean_object* v_names_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_array_get_size(v_names_203_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_nat_dec_lt(v___x_208_, v___x_209_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
return v___x_212_;
}
else
{
uint8_t v___x_213_; 
v___x_213_ = lean_nat_dec_le(v___x_209_, v___x_209_);
if (v___x_213_ == 0)
{
if (v___x_211_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_210_);
return v___x_214_;
}
else
{
size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; 
v___x_215_ = ((size_t)0ULL);
v___x_216_ = lean_usize_of_nat(v___x_209_);
v___x_217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_203_, v___x_215_, v___x_216_, v___x_210_, v_a_204_, v_a_205_, v_a_206_);
return v___x_217_;
}
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_209_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_names_203_, v___x_218_, v___x_219_, v___x_210_, v_a_204_, v_a_205_, v_a_206_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(lean_object* v_code_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_declName_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; 
if (lean_obj_tag(v_code_221_) == 0)
{
lean_object* v_decl_235_; lean_object* v_value_236_; 
v_decl_235_ = lean_ctor_get(v_code_221_, 0);
lean_inc_ref(v_decl_235_);
lean_dec_ref_known(v_code_221_, 2);
v_value_236_ = lean_ctor_get(v_decl_235_, 3);
lean_inc(v_value_236_);
lean_dec_ref(v_decl_235_);
switch(lean_obj_tag(v_value_236_))
{
case 3:
{
lean_object* v_declName_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_declName_237_ = lean_ctor_get(v_value_236_, 0);
lean_inc(v_declName_237_);
lean_dec_ref_known(v_value_236_, 3);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_mk_empty_array_with_capacity(v___x_238_);
v___x_240_ = lean_array_push(v___x_239_, v_declName_237_);
v___x_241_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_240_, v_a_222_, v_a_223_, v_a_224_);
lean_dec_ref(v___x_240_);
return v___x_241_;
}
case 9:
{
lean_object* v_fn_242_; 
v_fn_242_ = lean_ctor_get(v_value_236_, 0);
lean_inc(v_fn_242_);
lean_dec_ref_known(v_value_236_, 2);
v_declName_227_ = v_fn_242_;
v___y_228_ = v_a_222_;
v___y_229_ = v_a_223_;
v___y_230_ = v_a_224_;
goto v___jp_226_;
}
case 10:
{
lean_object* v_fn_243_; 
v_fn_243_ = lean_ctor_get(v_value_236_, 0);
lean_inc(v_fn_243_);
lean_dec_ref_known(v_value_236_, 2);
v_declName_227_ = v_fn_243_;
v___y_228_ = v_a_222_;
v___y_229_ = v_a_223_;
v___y_230_ = v_a_224_;
goto v___jp_226_;
}
default: 
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_value_236_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec_ref(v_code_221_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
v___jp_226_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_231_ = lean_unsigned_to_nat(1u);
v___x_232_ = lean_mk_empty_array_with_capacity(v___x_231_);
v___x_233_ = lean_array_push(v___x_232_, v_declName_227_);
v___x_234_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v___x_233_, v___y_228_, v___y_229_, v___y_230_);
lean_dec_ref(v___x_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(uint8_t v_pu_248_, lean_object* v_as_249_, size_t v_i_250_, size_t v_stop_251_, lean_object* v_b_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___y_258_; uint8_t v___x_263_; 
v___x_263_ = lean_usize_dec_eq(v_i_250_, v_stop_251_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_array_uget_borrowed(v_as_249_, v_i_250_);
switch(lean_obj_tag(v___x_264_))
{
case 0:
{
lean_object* v_code_265_; lean_object* v___x_266_; 
v_code_265_ = lean_ctor_get(v___x_264_, 2);
lean_inc_ref(v_code_265_);
v___x_266_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_248_, v_code_265_, v___y_253_, v___y_254_, v___y_255_);
v___y_258_ = v___x_266_;
goto v___jp_257_;
}
case 1:
{
lean_object* v_code_267_; lean_object* v___x_268_; 
v_code_267_ = lean_ctor_get(v___x_264_, 1);
lean_inc_ref(v_code_267_);
v___x_268_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_248_, v_code_267_, v___y_253_, v___y_254_, v___y_255_);
v___y_258_ = v___x_268_;
goto v___jp_257_;
}
default: 
{
lean_object* v_code_269_; lean_object* v___x_270_; 
v_code_269_ = lean_ctor_get(v___x_264_, 0);
lean_inc_ref(v_code_269_);
v___x_270_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_248_, v_code_269_, v___y_253_, v___y_254_, v___y_255_);
v___y_258_ = v___x_270_;
goto v___jp_257_;
}
}
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v_b_252_);
return v___x_271_;
}
v___jp_257_:
{
if (lean_obj_tag(v___y_258_) == 0)
{
lean_object* v_a_259_; size_t v___x_260_; size_t v___x_261_; 
v_a_259_ = lean_ctor_get(v___y_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v___y_258_, 1);
v___x_260_ = ((size_t)1ULL);
v___x_261_ = lean_usize_add(v_i_250_, v___x_260_);
v_i_250_ = v___x_261_;
v_b_252_ = v_a_259_;
goto _start;
}
else
{
return v___y_258_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(uint8_t v_pu_272_, lean_object* v_c_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; 
lean_inc_ref(v_c_273_);
v___x_278_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_c_273_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_331_; 
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_278_, 0);
lean_dec(v_unused_332_);
v___x_280_ = v___x_278_;
v_isShared_281_ = v_isSharedCheck_331_;
goto v_resetjp_279_;
}
else
{
lean_dec(v___x_278_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_331_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
switch(lean_obj_tag(v_c_273_))
{
case 0:
{
lean_object* v_k_282_; 
lean_del_object(v___x_280_);
v_k_282_ = lean_ctor_get(v_c_273_, 1);
lean_inc_ref(v_k_282_);
lean_dec_ref_known(v_c_273_, 2);
v_c_273_ = v_k_282_;
goto _start;
}
case 1:
{
lean_object* v_decl_284_; lean_object* v_k_285_; lean_object* v_value_286_; lean_object* v___x_287_; 
lean_del_object(v___x_280_);
v_decl_284_ = lean_ctor_get(v_c_273_, 0);
lean_inc_ref(v_decl_284_);
v_k_285_ = lean_ctor_get(v_c_273_, 1);
lean_inc_ref(v_k_285_);
lean_dec_ref_known(v_c_273_, 2);
v_value_286_ = lean_ctor_get(v_decl_284_, 4);
lean_inc_ref(v_value_286_);
lean_dec_ref(v_decl_284_);
v___x_287_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_272_, v_value_286_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_dec_ref_known(v___x_287_, 1);
v_c_273_ = v_k_285_;
goto _start;
}
else
{
lean_dec_ref(v_k_285_);
return v___x_287_;
}
}
case 2:
{
lean_object* v_decl_289_; lean_object* v_k_290_; lean_object* v_value_291_; lean_object* v___x_292_; 
lean_del_object(v___x_280_);
v_decl_289_ = lean_ctor_get(v_c_273_, 0);
lean_inc_ref(v_decl_289_);
v_k_290_ = lean_ctor_get(v_c_273_, 1);
lean_inc_ref(v_k_290_);
lean_dec_ref_known(v_c_273_, 2);
v_value_291_ = lean_ctor_get(v_decl_289_, 4);
lean_inc_ref(v_value_291_);
lean_dec_ref(v_decl_289_);
v___x_292_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_272_, v_value_291_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_dec_ref_known(v___x_292_, 1);
v_c_273_ = v_k_290_;
goto _start;
}
else
{
lean_dec_ref(v_k_290_);
return v___x_292_;
}
}
case 4:
{
lean_object* v_cases_294_; lean_object* v_alts_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_cases_294_ = lean_ctor_get(v_c_273_, 0);
lean_inc_ref(v_cases_294_);
lean_dec_ref_known(v_c_273_, 1);
v_alts_295_ = lean_ctor_get(v_cases_294_, 3);
lean_inc_ref(v_alts_295_);
lean_dec_ref(v_cases_294_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_array_get_size(v_alts_295_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_nat_dec_lt(v___x_296_, v___x_297_);
if (v___x_299_ == 0)
{
lean_object* v___x_301_; 
lean_dec_ref(v_alts_295_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_298_);
v___x_301_ = v___x_280_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_298_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
else
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_le(v___x_297_, v___x_297_);
if (v___x_303_ == 0)
{
if (v___x_299_ == 0)
{
lean_object* v___x_305_; 
lean_dec_ref(v_alts_295_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_298_);
v___x_305_ = v___x_280_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_298_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
lean_del_object(v___x_280_);
v___x_307_ = ((size_t)0ULL);
v___x_308_ = lean_usize_of_nat(v___x_297_);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_272_, v_alts_295_, v___x_307_, v___x_308_, v___x_298_, v___y_274_, v___y_275_, v___y_276_);
lean_dec_ref(v_alts_295_);
return v___x_309_;
}
}
else
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
lean_del_object(v___x_280_);
v___x_310_ = ((size_t)0ULL);
v___x_311_ = lean_usize_of_nat(v___x_297_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_272_, v_alts_295_, v___x_310_, v___x_311_, v___x_298_, v___y_274_, v___y_275_, v___y_276_);
lean_dec_ref(v_alts_295_);
return v___x_312_;
}
}
}
case 7:
{
lean_object* v_k_313_; 
lean_del_object(v___x_280_);
v_k_313_ = lean_ctor_get(v_c_273_, 3);
lean_inc_ref(v_k_313_);
lean_dec_ref_known(v_c_273_, 4);
v_c_273_ = v_k_313_;
goto _start;
}
case 8:
{
lean_object* v_k_315_; 
lean_del_object(v___x_280_);
v_k_315_ = lean_ctor_get(v_c_273_, 3);
lean_inc_ref(v_k_315_);
lean_dec_ref_known(v_c_273_, 4);
v_c_273_ = v_k_315_;
goto _start;
}
case 9:
{
lean_object* v_k_317_; 
lean_del_object(v___x_280_);
v_k_317_ = lean_ctor_get(v_c_273_, 5);
lean_inc_ref(v_k_317_);
lean_dec_ref_known(v_c_273_, 6);
v_c_273_ = v_k_317_;
goto _start;
}
case 10:
{
lean_object* v_k_319_; 
lean_del_object(v___x_280_);
v_k_319_ = lean_ctor_get(v_c_273_, 2);
lean_inc_ref(v_k_319_);
lean_dec_ref_known(v_c_273_, 3);
v_c_273_ = v_k_319_;
goto _start;
}
case 11:
{
lean_object* v_k_321_; 
lean_del_object(v___x_280_);
v_k_321_ = lean_ctor_get(v_c_273_, 2);
lean_inc_ref(v_k_321_);
lean_dec_ref_known(v_c_273_, 3);
v_c_273_ = v_k_321_;
goto _start;
}
case 12:
{
lean_object* v_k_323_; 
lean_del_object(v___x_280_);
v_k_323_ = lean_ctor_get(v_c_273_, 3);
lean_inc_ref(v_k_323_);
lean_dec_ref_known(v_c_273_, 4);
v_c_273_ = v_k_323_;
goto _start;
}
case 13:
{
lean_object* v_k_325_; 
lean_del_object(v___x_280_);
v_k_325_ = lean_ctor_get(v_c_273_, 1);
lean_inc_ref(v_k_325_);
lean_dec_ref_known(v_c_273_, 2);
v_c_273_ = v_k_325_;
goto _start;
}
default: 
{
lean_object* v___x_327_; lean_object* v___x_329_; 
lean_dec_ref(v_c_273_);
v___x_327_ = lean_box(0);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_327_);
v___x_329_ = v___x_280_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
else
{
lean_dec_ref(v_c_273_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___lam__0(uint8_t v___x_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v___x_333_, v_x_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1___boxed(lean_object* v_pu_340_, lean_object* v_as_341_, lean_object* v_i_342_, lean_object* v_stop_343_, lean_object* v_b_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
uint8_t v_pu_boxed_349_; size_t v_i_boxed_350_; size_t v_stop_boxed_351_; lean_object* v_res_352_; 
v_pu_boxed_349_ = lean_unbox(v_pu_340_);
v_i_boxed_350_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_stop_boxed_351_ = lean_unbox_usize(v_stop_343_);
lean_dec(v_stop_343_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0_spec__1(v_pu_boxed_349_, v_as_341_, v_i_boxed_350_, v_stop_boxed_351_, v_b_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v_as_341_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go___boxed(lean_object* v_names_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_names_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_names_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode___boxed(lean_object* v_code_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_visitCode(v_code_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0___boxed(lean_object* v_pu_365_, lean_object* v_c_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
uint8_t v_pu_boxed_371_; lean_object* v_res_372_; 
v_pu_boxed_371_ = lean_unbox(v_pu_365_);
v_res_372_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Code_forM_go___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__0(v_pu_boxed_371_, v_c_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3___boxed(lean_object* v_as_373_, lean_object* v_i_374_, lean_object* v_stop_375_, lean_object* v_b_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
size_t v_i_boxed_381_; size_t v_stop_boxed_382_; lean_object* v_res_383_; 
v_i_boxed_381_ = lean_unbox_usize(v_i_374_);
lean_dec(v_i_374_);
v_stop_boxed_382_ = lean_unbox_usize(v_stop_375_);
lean_dec(v_stop_375_);
v_res_383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__3(v_as_373_, v_i_boxed_381_, v_stop_boxed_382_, v_b_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v_as_373_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(uint8_t v_pu_384_, lean_object* v_f_385_, lean_object* v_v_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___redArg(v_f_385_, v_v_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1___boxed(lean_object* v_pu_392_, lean_object* v_f_393_, lean_object* v_v_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
uint8_t v_pu_boxed_399_; lean_object* v_res_400_; 
v_pu_boxed_399_ = lean_unbox(v_pu_392_);
v_res_400_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00__private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go_spec__1(v_pu_boxed_399_, v_f_393_, v_v_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
return v_res_400_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = ((lean_object*)(l_Lean_Compiler_LCNF_collectUsedDecls___closed__0));
v___x_404_ = l_Lean_NameSet_empty;
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedDecls(lean_object* v_decls_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_obj_once(&l_Lean_Compiler_LCNF_collectUsedDecls___closed__1, &l_Lean_Compiler_LCNF_collectUsedDecls___closed__1_once, _init_l_Lean_Compiler_LCNF_collectUsedDecls___closed__1);
v___x_411_ = lean_st_mk_ref(v___x_410_);
v___x_412_ = l___private_Lean_Compiler_LCNF_EmitUtil_0__Lean_Compiler_LCNF_collectUsedDecls_go(v_decls_406_, v___x_411_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_423_; 
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_412_, 0);
lean_dec(v_unused_424_);
v___x_414_ = v___x_412_;
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
else
{
lean_dec(v___x_412_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v_localDecls_417_; lean_object* v_extSigs_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_416_ = lean_st_ref_get(v___x_411_);
lean_dec(v___x_411_);
v_localDecls_417_ = lean_ctor_get(v___x_416_, 1);
lean_inc_ref(v_localDecls_417_);
v_extSigs_418_ = lean_ctor_get(v___x_416_, 2);
lean_inc_ref(v_extSigs_418_);
lean_dec(v___x_416_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v_localDecls_417_);
lean_ctor_set(v___x_419_, 1, v_extSigs_418_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_419_);
v___x_421_ = v___x_414_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v___x_411_);
v_a_425_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_412_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_412_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_collectUsedDecls___boxed(lean_object* v_decls_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Compiler_LCNF_collectUsedDecls(v_decls_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_decls_433_);
return v_res_437_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(lean_object* v_modulePrefix_438_, lean_object* v_as_439_, size_t v_i_440_, size_t v_stop_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_eq(v_i_440_, v_stop_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v_toImport_444_; uint8_t v_irPhases_445_; uint8_t v___x_446_; uint8_t v___y_448_; uint8_t v___x_452_; uint8_t v___x_453_; 
v___x_443_ = lean_array_uget_borrowed(v_as_439_, v_i_440_);
v_toImport_444_ = lean_ctor_get(v___x_443_, 0);
v_irPhases_445_ = lean_ctor_get_uint8(v___x_443_, sizeof(void*)*1);
v___x_446_ = 1;
v___x_452_ = 1;
v___x_453_ = l_Lean_instBEqIRPhases_beq(v_irPhases_445_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v_module_454_; uint8_t v___x_455_; 
v_module_454_ = lean_ctor_get(v_toImport_444_, 0);
v___x_455_ = l_Lean_Name_isPrefixOf(v_modulePrefix_438_, v_module_454_);
v___y_448_ = v___x_455_;
goto v___jp_447_;
}
else
{
v___y_448_ = v___x_442_;
goto v___jp_447_;
}
v___jp_447_:
{
if (v___y_448_ == 0)
{
size_t v___x_449_; size_t v___x_450_; 
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_440_, v___x_449_);
v_i_440_ = v___x_450_;
goto _start;
}
else
{
return v___x_446_;
}
}
}
else
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0___boxed(lean_object* v_modulePrefix_457_, lean_object* v_as_458_, lean_object* v_i_459_, lean_object* v_stop_460_){
_start:
{
size_t v_i_boxed_461_; size_t v_stop_boxed_462_; uint8_t v_res_463_; lean_object* v_r_464_; 
v_i_boxed_461_ = lean_unbox_usize(v_i_459_);
lean_dec(v_i_459_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_460_);
lean_dec(v_stop_460_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_457_, v_as_458_, v_i_boxed_461_, v_stop_boxed_462_);
lean_dec_ref(v_as_458_);
lean_dec(v_modulePrefix_457_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_usesModuleFrom(lean_object* v_env_465_, lean_object* v_modulePrefix_466_){
_start:
{
lean_object* v___x_467_; lean_object* v_modules_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_467_ = l_Lean_Environment_header(v_env_465_);
v_modules_468_ = lean_ctor_get(v___x_467_, 3);
lean_inc_ref(v_modules_468_);
lean_dec_ref(v___x_467_);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_array_get_size(v_modules_468_);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_dec_ref(v_modules_468_);
return v___x_471_;
}
else
{
if (v___x_471_ == 0)
{
lean_dec_ref(v_modules_468_);
return v___x_471_;
}
else
{
size_t v___x_472_; size_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_470_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_usesModuleFrom_spec__0(v_modulePrefix_466_, v_modules_468_, v___x_472_, v___x_473_);
lean_dec_ref(v_modules_468_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_usesModuleFrom___boxed(lean_object* v_env_475_, lean_object* v_modulePrefix_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Lean_Compiler_LCNF_usesModuleFrom(v_env_475_, v_modulePrefix_476_);
lean_dec(v_modulePrefix_476_);
lean_dec_ref(v_env_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_EmitUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
