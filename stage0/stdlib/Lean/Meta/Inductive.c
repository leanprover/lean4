// Lean compiler output
// Module: Lean.Meta.Inductive
// Imports: public import Lean.Meta.Basic
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
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_compatibleCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_compatibleCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0_spec__1(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_instMonadEIO(lean_box(0));
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_toApplicative_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_121_; 
v___x_58_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__0);
v___x_59_ = l_StateRefT_x27_instMonad___redArg(v___x_58_);
v_toApplicative_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_121_ == 0)
{
lean_object* v_unused_122_; 
v_unused_122_ = lean_ctor_get(v___x_59_, 1);
lean_dec(v_unused_122_);
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_121_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_toApplicative_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_121_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_toFunctor_64_; lean_object* v_toSeq_65_; lean_object* v_toSeqLeft_66_; lean_object* v_toSeqRight_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_119_; 
v_toFunctor_64_ = lean_ctor_get(v_toApplicative_60_, 0);
v_toSeq_65_ = lean_ctor_get(v_toApplicative_60_, 2);
v_toSeqLeft_66_ = lean_ctor_get(v_toApplicative_60_, 3);
v_toSeqRight_67_ = lean_ctor_get(v_toApplicative_60_, 4);
v_isSharedCheck_119_ = !lean_is_exclusive(v_toApplicative_60_);
if (v_isSharedCheck_119_ == 0)
{
lean_object* v_unused_120_; 
v_unused_120_ = lean_ctor_get(v_toApplicative_60_, 1);
lean_dec(v_unused_120_);
v___x_69_ = v_toApplicative_60_;
v_isShared_70_ = v_isSharedCheck_119_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_toSeqRight_67_);
lean_inc(v_toSeqLeft_66_);
lean_inc(v_toSeq_65_);
lean_inc(v_toFunctor_64_);
lean_dec(v_toApplicative_60_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_119_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___f_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___f_76_; lean_object* v___f_77_; lean_object* v___f_78_; lean_object* v___x_80_; 
v___f_71_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__1));
v___f_72_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_64_);
v___f_73_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_73_, 0, v_toFunctor_64_);
v___f_74_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_74_, 0, v_toFunctor_64_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v___f_73_);
lean_ctor_set(v___x_75_, 1, v___f_74_);
v___f_76_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_76_, 0, v_toSeqRight_67_);
v___f_77_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_77_, 0, v_toSeqLeft_66_);
v___f_78_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_78_, 0, v_toSeq_65_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 4, v___f_76_);
lean_ctor_set(v___x_69_, 3, v___f_77_);
lean_ctor_set(v___x_69_, 2, v___f_78_);
lean_ctor_set(v___x_69_, 1, v___f_71_);
lean_ctor_set(v___x_69_, 0, v___x_75_);
v___x_80_ = v___x_69_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___f_71_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v___f_78_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v___f_77_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___f_76_);
v___x_80_ = v_reuseFailAlloc_118_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_82_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___f_72_);
lean_ctor_set(v___x_62_, 0, v___x_80_);
v___x_82_ = v___x_62_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___f_72_);
v___x_82_ = v_reuseFailAlloc_117_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v_toApplicative_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_115_; 
v___x_83_ = l_StateRefT_x27_instMonad___redArg(v___x_82_);
v_toApplicative_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v___x_83_, 1);
lean_dec(v_unused_116_);
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_115_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_toApplicative_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_115_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_toFunctor_88_; lean_object* v_toSeq_89_; lean_object* v_toSeqLeft_90_; lean_object* v_toSeqRight_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_113_; 
v_toFunctor_88_ = lean_ctor_get(v_toApplicative_84_, 0);
v_toSeq_89_ = lean_ctor_get(v_toApplicative_84_, 2);
v_toSeqLeft_90_ = lean_ctor_get(v_toApplicative_84_, 3);
v_toSeqRight_91_ = lean_ctor_get(v_toApplicative_84_, 4);
v_isSharedCheck_113_ = !lean_is_exclusive(v_toApplicative_84_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_toApplicative_84_, 1);
lean_dec(v_unused_114_);
v___x_93_ = v_toApplicative_84_;
v_isShared_94_ = v_isSharedCheck_113_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_toSeqRight_91_);
lean_inc(v_toSeqLeft_90_);
lean_inc(v_toSeq_89_);
lean_inc(v_toFunctor_88_);
lean_dec(v_toApplicative_84_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_113_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___f_95_; lean_object* v___f_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___f_102_; lean_object* v___x_104_; 
v___f_95_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__3));
v___f_96_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_88_);
v___f_97_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_97_, 0, v_toFunctor_88_);
v___f_98_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_98_, 0, v_toFunctor_88_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___f_97_);
lean_ctor_set(v___x_99_, 1, v___f_98_);
v___f_100_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_100_, 0, v_toSeqRight_91_);
v___f_101_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_101_, 0, v_toSeqLeft_90_);
v___f_102_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_102_, 0, v_toSeq_89_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___f_100_);
lean_ctor_set(v___x_93_, 3, v___f_101_);
lean_ctor_set(v___x_93_, 2, v___f_102_);
lean_ctor_set(v___x_93_, 1, v___f_95_);
lean_ctor_set(v___x_93_, 0, v___x_99_);
v___x_104_ = v___x_93_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_99_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___f_95_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v___f_102_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v___f_101_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v___f_100_);
v___x_104_ = v_reuseFailAlloc_112_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_106_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v___f_96_);
lean_ctor_set(v___x_86_, 0, v___x_104_);
v___x_106_ = v___x_86_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___f_96_);
v___x_106_ = v_reuseFailAlloc_111_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_1849__overap_109_; lean_object* v___x_110_; 
v___x_107_ = lean_box(0);
v___x_108_ = l_instInhabitedOfMonad___redArg(v___x_106_, v___x_107_);
v___x_1849__overap_109_ = lean_panic_fn(v___x_108_, v_msg_52_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
lean_inc(v___y_54_);
lean_inc_ref(v___y_53_);
v___x_110_ = lean_apply_5(v___x_1849__overap_109_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, lean_box(0));
return v___x_110_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1___boxed(lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1(v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_129_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__0));
v___x_132_ = l_Lean_stringToMessageData(v___x_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__2));
v___x_135_ = l_Lean_stringToMessageData(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_139_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__6));
v___x_140_ = lean_unsigned_to_nat(11u);
v___x_141_ = lean_unsigned_to_nat(122u);
v___x_142_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__5));
v___x_143_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__4));
v___x_144_ = l_mkPanicMessageWithDecl(v___x_143_, v___x_142_, v___x_141_, v___x_140_, v___x_139_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(lean_object* v_constName_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_159_; lean_object* v_env_160_; uint8_t v___x_161_; lean_object* v___x_162_; 
v___x_159_ = lean_st_ref_get(v___y_149_);
v_env_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc_ref(v_env_160_);
lean_dec(v___x_159_);
v___x_161_ = 0;
lean_inc(v_constName_145_);
v___x_162_ = l_Lean_Environment_findAsync_x3f(v_env_160_, v_constName_145_, v___x_161_);
if (lean_obj_tag(v___x_162_) == 1)
{
lean_object* v_val_163_; uint8_t v_kind_164_; 
v_val_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_val_163_);
lean_dec_ref(v___x_162_);
v_kind_164_ = lean_ctor_get_uint8(v_val_163_, sizeof(void*)*3);
if (v_kind_164_ == 6)
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_163_);
if (lean_obj_tag(v___x_165_) == 6)
{
lean_object* v_val_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
lean_dec(v_constName_145_);
v_val_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_val_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set_tag(v___x_168_, 0);
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_val_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec_ref(v___x_165_);
v___x_174_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__7);
v___x_175_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__1(v___x_174_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_184_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
if (lean_obj_tag(v_a_176_) == 0)
{
lean_del_object(v___x_178_);
goto v___jp_151_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_182_; 
lean_dec(v_constName_145_);
v_val_180_ = lean_ctor_get(v_a_176_, 0);
lean_inc(v_val_180_);
lean_dec_ref(v_a_176_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v_val_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_val_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec(v_constName_145_);
v_a_185_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_175_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_175_);
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
lean_dec(v_val_163_);
goto v___jp_151_;
}
}
else
{
lean_dec(v___x_162_);
goto v___jp_151_;
}
v___jp_151_:
{
lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_152_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__1);
v___x_153_ = 0;
v___x_154_ = l_Lean_MessageData_ofConstName(v_constName_145_, v___x_153_);
v___x_155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_152_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___closed__3);
v___x_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(v___x_157_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0___boxed(lean_object* v_constName_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(v_constName_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_compatibleCtors(lean_object* v_ctorName_u2081_200_, lean_object* v_ctorName_u2082_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(v_ctorName_u2081_200_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0(v_ctorName_u2082_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_251_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_251_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_251_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_251_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_toConstantVal_214_; lean_object* v_induct_215_; lean_object* v_toConstantVal_216_; lean_object* v_induct_217_; uint8_t v___x_218_; 
v_toConstantVal_214_ = lean_ctor_get(v_a_208_, 0);
lean_inc_ref(v_toConstantVal_214_);
v_induct_215_ = lean_ctor_get(v_a_208_, 1);
lean_inc(v_induct_215_);
lean_dec(v_a_208_);
v_toConstantVal_216_ = lean_ctor_get(v_a_210_, 0);
lean_inc_ref(v_toConstantVal_216_);
v_induct_217_ = lean_ctor_get(v_a_210_, 1);
lean_inc(v_induct_217_);
lean_dec(v_a_210_);
v___x_218_ = lean_name_eq(v_induct_215_, v_induct_217_);
lean_dec(v_induct_217_);
lean_dec(v_induct_215_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_221_; 
lean_dec_ref(v_toConstantVal_216_);
lean_dec_ref(v_toConstantVal_214_);
v___x_219_ = lean_box(v___x_218_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_219_);
v___x_221_ = v___x_212_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
else
{
lean_object* v_type_223_; uint8_t v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_212_);
v_type_223_ = lean_ctor_get(v_toConstantVal_214_, 2);
lean_inc_ref(v_type_223_);
lean_dec_ref(v_toConstantVal_214_);
v___x_224_ = 0;
v___x_225_ = l_Lean_Meta_forallMetaTelescope(v_type_223_, v___x_224_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v_snd_227_; lean_object* v_snd_228_; lean_object* v_type_229_; lean_object* v___x_230_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref(v___x_225_);
v_snd_227_ = lean_ctor_get(v_a_226_, 1);
lean_inc(v_snd_227_);
lean_dec(v_a_226_);
v_snd_228_ = lean_ctor_get(v_snd_227_, 1);
lean_inc(v_snd_228_);
lean_dec(v_snd_227_);
v_type_229_ = lean_ctor_get(v_toConstantVal_216_, 2);
lean_inc_ref(v_type_229_);
lean_dec_ref(v_toConstantVal_216_);
v___x_230_ = l_Lean_Meta_forallMetaTelescope(v_type_229_, v___x_224_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v_snd_232_; lean_object* v_snd_233_; lean_object* v___x_234_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
v_snd_232_ = lean_ctor_get(v_a_231_, 1);
lean_inc(v_snd_232_);
lean_dec(v_a_231_);
v_snd_233_ = lean_ctor_get(v_snd_232_, 1);
lean_inc(v_snd_233_);
lean_dec(v_snd_232_);
v___x_234_ = l_Lean_Meta_isExprDefEq(v_snd_228_, v_snd_233_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
return v___x_234_;
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v_snd_228_);
v_a_235_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_230_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_230_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec_ref(v_toConstantVal_216_);
v_a_243_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_225_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_225_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec(v_a_208_);
v_a_252_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_209_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_209_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec(v_ctorName_u2082_201_);
v_a_260_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_207_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_207_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_compatibleCtors___boxed(lean_object* v_ctorName_u2081_268_, lean_object* v_ctorName_u2082_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Meta_compatibleCtors(v_ctorName_u2081_268_, v_ctorName_u2082_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0(lean_object* v_00_u03b1_276_, lean_object* v_msg_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___redArg(v_msg_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_284_, lean_object* v_msg_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_Meta_compatibleCtors_spec__0_spec__0(v_00_u03b1_284_, v_msg_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Inductive(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Inductive(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Inductive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Inductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Inductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Inductive(builtin);
}
#ifdef __cplusplus
}
#endif
