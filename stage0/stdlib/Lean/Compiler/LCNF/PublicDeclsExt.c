// Lean compiler output
// Module: Lean.Compiler.LCNF.PublicDeclsExt
// Imports: public import Lean.Environment
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
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
static const lean_ctor_object l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_isDeclPublic___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l_Lean_Compiler_LCNF_isDeclPublic___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclPublic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(lean_object* v_newState_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
return v_x_2_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_33_; 
v_head_4_ = lean_ctor_get(v_x_3_, 0);
v_tail_5_ = lean_ctor_get(v_x_3_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_33_ == 0)
{
v___x_7_ = v_x_3_;
v_isShared_8_ = v_isSharedCheck_33_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_x_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_33_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_fst_9_; lean_object* v_snd_10_; uint8_t v___x_11_; 
v_fst_9_ = lean_ctor_get(v_x_2_, 0);
v_snd_10_ = lean_ctor_get(v_x_2_, 1);
v___x_11_ = l_Lean_NameSet_contains(v_snd_10_, v_head_4_);
if (v___x_11_ == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_29_; 
lean_inc(v_snd_10_);
lean_inc(v_fst_9_);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_29_ == 0)
{
lean_object* v_unused_30_; lean_object* v_unused_31_; 
v_unused_30_ = lean_ctor_get(v_x_2_, 1);
lean_dec(v_unused_30_);
v_unused_31_ = lean_ctor_get(v_x_2_, 0);
lean_dec(v_unused_31_);
v___x_13_ = v_x_2_;
v_isShared_14_ = v_isSharedCheck_29_;
goto v_resetjp_12_;
}
else
{
lean_dec(v_x_2_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_29_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_snd_15_; lean_object* v___x_17_; 
v_snd_15_ = lean_ctor_get(v_newState_1_, 1);
lean_inc(v_head_4_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_fst_9_);
v___x_17_ = v___x_7_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_head_4_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_fst_9_);
v___x_17_ = v_reuseFailAlloc_28_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
uint8_t v___x_18_; 
v___x_18_ = l_Lean_NameSet_contains(v_snd_15_, v_head_4_);
if (v___x_18_ == 0)
{
lean_object* v___x_20_; 
lean_dec(v_head_4_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_17_);
v___x_20_ = v___x_13_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_snd_10_);
v___x_20_ = v_reuseFailAlloc_22_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
v_x_2_ = v___x_20_;
v_x_3_ = v_tail_5_;
goto _start;
}
}
else
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = l_Lean_NameSet_insert(v_snd_10_, v_head_4_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_23_);
lean_ctor_set(v___x_13_, 0, v___x_17_);
v___x_25_ = v___x_13_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v___x_23_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
v_x_2_ = v___x_25_;
v_x_3_ = v_tail_5_;
goto _start;
}
}
}
}
}
else
{
lean_del_object(v___x_7_);
lean_dec(v_head_4_);
v_x_3_ = v_tail_5_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0___boxed(lean_object* v_newState_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(v_newState_34_, v_x_35_, v_x_36_);
lean_dec_ref(v_newState_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(lean_object* v_oldState_40_, lean_object* v_newState_41_, lean_object* v_x_42_, lean_object* v_s_43_){
_start:
{
lean_object* v_fst_44_; lean_object* v_fst_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v_newEntries_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_fst_44_ = lean_ctor_get(v_newState_41_, 0);
v_fst_45_ = lean_ctor_get(v_oldState_40_, 0);
v___x_46_ = l_List_lengthTR___redArg(v_fst_44_);
v___x_47_ = l_List_lengthTR___redArg(v_fst_45_);
v___x_48_ = lean_nat_sub(v___x_46_, v___x_47_);
lean_dec(v___x_47_);
lean_dec(v___x_46_);
v___x_49_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___closed__0));
lean_inc(v_fst_44_);
v_newEntries_50_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_fst_44_, v_fst_44_, v___x_48_, v___x_49_);
v___x_51_ = l_List_reverse___redArg(v_newEntries_50_);
v___x_52_ = l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(v_newState_41_, v_s_43_, v___x_51_);
lean_dec_ref(v_newState_41_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed(lean_object* v_oldState_53_, lean_object* v_newState_54_, lean_object* v_x_55_, lean_object* v_s_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(v_oldState_53_, v_newState_54_, v_x_55_, v_s_56_);
lean_dec(v_x_55_);
lean_dec_ref(v_oldState_53_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(lean_object* v___x_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed(lean_object* v___x_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(v___x_61_);
return v_res_63_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = l_Lean_NameSet_empty;
v___x_66_ = lean_box(0);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2(void){
_start:
{
lean_object* v___x_68_; lean_object* v___f_69_; 
v___x_68_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1, &l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1_once, _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1);
v___f_69_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed), 2, 1);
lean_closure_set(v___f_69_, 0, v___x_68_);
return v___f_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt(){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___f_73_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2, &l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2_once, _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2);
v___x_74_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3));
v___x_75_ = lean_box(0);
v___x_76_ = l_Lean_registerEnvExtension___redArg(v___f_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2____boxed(lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
return v_res_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object* v_env_87_, lean_object* v_declName_88_){
_start:
{
lean_object* v___y_90_; lean_object* v___x_98_; uint8_t v_isModule_99_; 
v___x_98_ = l_Lean_Environment_header(v_env_87_);
v_isModule_99_ = lean_ctor_get_uint8(v___x_98_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_98_);
if (v_isModule_99_ == 0)
{
uint8_t v___x_100_; 
lean_dec_ref(v_env_87_);
v___x_100_ = 1;
return v___x_100_;
}
else
{
if (lean_obj_tag(v_declName_88_) == 1)
{
lean_object* v_pre_101_; lean_object* v_str_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_pre_101_ = lean_ctor_get(v_declName_88_, 0);
v_str_102_ = lean_ctor_get(v_declName_88_, 1);
v___x_103_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclPublic___closed__1));
v___x_104_ = lean_string_dec_eq(v_str_102_, v___x_103_);
if (v___x_104_ == 0)
{
v___y_90_ = v_declName_88_;
goto v___jp_89_;
}
else
{
v___y_90_ = v_pre_101_;
goto v___jp_89_;
}
}
else
{
v___y_90_ = v_declName_88_;
goto v___jp_89_;
}
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v_asyncMode_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_snd_96_; uint8_t v___x_97_; 
v___x_91_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
v_asyncMode_92_ = lean_ctor_get(v___x_91_, 2);
v___x_93_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclPublic___closed__0));
v___x_94_ = lean_box(0);
v___x_95_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_93_, v___x_91_, v_env_87_, v_asyncMode_92_, v___x_94_);
v_snd_96_ = lean_ctor_get(v___x_95_, 1);
lean_inc(v_snd_96_);
lean_dec(v___x_95_);
v___x_97_ = l_Lean_NameSet_contains(v_snd_96_, v___y_90_);
lean_dec(v_snd_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclPublic___boxed(lean_object* v_env_105_, lean_object* v_declName_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_105_, v_declName_106_);
lean_dec(v_declName_106_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic___lam__0(lean_object* v_declName_109_, lean_object* v_s_110_){
_start:
{
lean_object* v_fst_111_; lean_object* v_snd_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_121_; 
v_fst_111_ = lean_ctor_get(v_s_110_, 0);
v_snd_112_ = lean_ctor_get(v_s_110_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_s_110_);
if (v_isSharedCheck_121_ == 0)
{
v___x_114_ = v_s_110_;
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_snd_112_);
lean_inc(v_fst_111_);
lean_dec(v_s_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
lean_inc(v_declName_109_);
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v_declName_109_);
lean_ctor_set(v___x_116_, 1, v_fst_111_);
v___x_117_ = l_Lean_NameSet_insert(v_snd_112_, v_declName_109_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_117_);
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_119_ = v___x_114_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object* v_env_122_, lean_object* v_declName_123_){
_start:
{
uint8_t v___x_124_; 
lean_inc_ref(v_env_122_);
v___x_124_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_122_, v_declName_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v_asyncMode_126_; lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_125_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
v_asyncMode_126_ = lean_ctor_get(v___x_125_, 2);
v___f_127_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_setDeclPublic___lam__0), 2, 1);
lean_closure_set(v___f_127_, 0, v_declName_123_);
v___x_128_ = lean_box(0);
v___x_129_ = l_Lean_EnvExtension_modifyState___redArg(v___x_125_, v_env_122_, v___f_127_, v_asyncMode_126_, v___x_128_);
return v___x_129_;
}
else
{
lean_dec(v_declName_123_);
return v_env_122_;
}
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
}
#ifdef __cplusplus
}
#endif
