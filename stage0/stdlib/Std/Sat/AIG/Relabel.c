// Lean compiler output
// Module: Std.Sat.AIG.Relabel
// Imports: public import Std.Sat.AIG.Lemmas import Init.ByCases import Init.Omega
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Std_Sat_AIG_relabel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__0 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__0_value;
static const lean_closure_object l_Std_Sat_AIG_relabel___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__1 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__1_value;
static const lean_closure_object l_Std_Sat_AIG_relabel___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__2 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__2_value;
static const lean_closure_object l_Std_Sat_AIG_relabel___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__3 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__3_value;
static const lean_closure_object l_Std_Sat_AIG_relabel___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__4 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__4_value;
static const lean_closure_object l_Std_Sat_AIG_relabel___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__5 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__5_value;
static const lean_closure_object l_Std_Sat_AIG_relabel___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__6 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__6_value;
static const lean_ctor_object l_Std_Sat_AIG_relabel___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__0_value),((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__1_value)}};
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__7 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__7_value;
static const lean_ctor_object l_Std_Sat_AIG_relabel___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__7_value),((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__2_value),((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__3_value),((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__4_value),((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__5_value)}};
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__8 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__8_value;
static const lean_ctor_object l_Std_Sat_AIG_relabel___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__8_value),((lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__6_value)}};
static const lean_object* l_Std_Sat_AIG_relabel___redArg___closed__9 = (const lean_object*)&l_Std_Sat_AIG_relabel___redArg___closed__9_value;
static lean_once_cell_t l_Std_Sat_AIG_relabel___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__10;
static lean_once_cell_t l_Std_Sat_AIG_relabel___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_AIG_relabel___redArg___closed__11;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel___redArg(lean_object* v_r_1_, lean_object* v_decl_2_){
_start:
{
switch(lean_obj_tag(v_decl_2_))
{
case 0:
{
lean_object* v___x_3_; 
lean_dec(v_r_1_);
v___x_3_ = lean_box(0);
return v___x_3_;
}
case 1:
{
lean_object* v_idx_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_12_; 
v_idx_4_ = lean_ctor_get(v_decl_2_, 0);
v_isSharedCheck_12_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_12_ == 0)
{
v___x_6_ = v_decl_2_;
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_idx_4_);
lean_dec(v_decl_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_10_; 
v___x_8_ = lean_apply_1(v_r_1_, v_idx_4_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 0, v___x_8_);
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v___x_8_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
default: 
{
lean_object* v_l_13_; lean_object* v_r_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
lean_dec(v_r_1_);
v_l_13_ = lean_ctor_get(v_decl_2_, 0);
v_r_14_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v_decl_2_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_r_14_);
lean_inc(v_l_13_);
lean_dec(v_decl_2_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_l_13_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_r_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Decl_relabel(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_r_24_, lean_object* v_decl_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_24_, v_decl_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter___redArg(lean_object* v_decl_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_, lean_object* v_h__3_30_){
_start:
{
switch(lean_obj_tag(v_decl_27_))
{
case 0:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_h__3_30_);
lean_dec(v_h__2_29_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_apply_1(v_h__1_28_, v___x_31_);
return v___x_32_;
}
case 1:
{
lean_object* v_idx_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_30_);
lean_dec(v_h__1_28_);
v_idx_33_ = lean_ctor_get(v_decl_27_, 0);
lean_inc(v_idx_33_);
lean_dec_ref(v_decl_27_);
v___x_34_ = lean_apply_1(v_h__2_29_, v_idx_33_);
return v___x_34_;
}
default: 
{
lean_object* v_l_35_; lean_object* v_r_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_29_);
lean_dec(v_h__1_28_);
v_l_35_ = lean_ctor_get(v_decl_27_, 0);
lean_inc(v_l_35_);
v_r_36_ = lean_ctor_get(v_decl_27_, 1);
lean_inc(v_r_36_);
lean_dec_ref(v_decl_27_);
v___x_37_ = lean_apply_2(v_h__3_30_, v_l_35_, v_r_36_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_AIG_Relabel_0__Std_Sat_AIG_Decl_relabel_match__1_splitter(lean_object* v_00_u03b1_38_, lean_object* v_motive_39_, lean_object* v_decl_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_, lean_object* v_h__3_43_){
_start:
{
switch(lean_obj_tag(v_decl_40_))
{
case 0:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_h__3_43_);
lean_dec(v_h__2_42_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_apply_1(v_h__1_41_, v___x_44_);
return v___x_45_;
}
case 1:
{
lean_object* v_idx_46_; lean_object* v___x_47_; 
lean_dec(v_h__3_43_);
lean_dec(v_h__1_41_);
v_idx_46_ = lean_ctor_get(v_decl_40_, 0);
lean_inc(v_idx_46_);
lean_dec_ref(v_decl_40_);
v___x_47_ = lean_apply_1(v_h__2_42_, v_idx_46_);
return v___x_47_;
}
default: 
{
lean_object* v_l_48_; lean_object* v_r_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_42_);
lean_dec(v_h__1_41_);
v_l_48_ = lean_ctor_get(v_decl_40_, 0);
lean_inc(v_l_48_);
v_r_49_ = lean_ctor_get(v_decl_40_, 1);
lean_inc(v_r_49_);
lean_dec_ref(v_decl_40_);
v___x_50_ = lean_apply_2(v_h__3_43_, v_l_48_, v_r_49_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___redArg___lam__0(lean_object* v_r_51_, lean_object* v_x_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_51_, v_x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__10(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = lean_box(0);
v___x_74_ = lean_unsigned_to_nat(16u);
v___x_75_ = lean_mk_array(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Std_Sat_AIG_relabel___redArg___closed__11(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v_cache_78_; 
v___x_76_ = lean_obj_once(&l_Std_Sat_AIG_relabel___redArg___closed__10, &l_Std_Sat_AIG_relabel___redArg___closed__10_once, _init_l_Std_Sat_AIG_relabel___redArg___closed__10);
v___x_77_ = lean_unsigned_to_nat(0u);
v_cache_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cache_78_, 0, v___x_77_);
lean_ctor_set(v_cache_78_, 1, v___x_76_);
return v_cache_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___redArg(lean_object* v_r_79_, lean_object* v_aig_80_){
_start:
{
lean_object* v_decls_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_94_; 
v_decls_81_ = lean_ctor_get(v_aig_80_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v_aig_80_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; 
v_unused_95_ = lean_ctor_get(v_aig_80_, 1);
lean_dec(v_unused_95_);
v___x_83_ = v_aig_80_;
v_isShared_84_ = v_isSharedCheck_94_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_decls_81_);
lean_dec(v_aig_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_94_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___f_85_; lean_object* v___x_86_; size_t v_sz_87_; size_t v___x_88_; lean_object* v_decls_89_; lean_object* v_cache_90_; lean_object* v___x_92_; 
v___f_85_ = lean_alloc_closure((void*)(l_Std_Sat_AIG_relabel___redArg___lam__0), 2, 1);
lean_closure_set(v___f_85_, 0, v_r_79_);
v___x_86_ = ((lean_object*)(l_Std_Sat_AIG_relabel___redArg___closed__9));
v_sz_87_ = lean_array_size(v_decls_81_);
v___x_88_ = ((size_t)0ULL);
v_decls_89_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_85_, v_sz_87_, v___x_88_, v_decls_81_);
v_cache_90_ = lean_obj_once(&l_Std_Sat_AIG_relabel___redArg___closed__11, &l_Std_Sat_AIG_relabel___redArg___closed__11_once, _init_l_Std_Sat_AIG_relabel___redArg___closed__11);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_cache_90_);
lean_ctor_set(v___x_83_, 0, v_decls_89_);
v___x_92_ = v___x_83_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_decls_89_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_cache_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel(lean_object* v_00_u03b1_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_00_u03b2_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_r_102_, lean_object* v_aig_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_Sat_AIG_relabel___redArg(v_r_102_, v_aig_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_relabel___boxed(lean_object* v_00_u03b1_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_00_u03b2_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_r_111_, lean_object* v_aig_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_Sat_AIG_relabel(v_00_u03b1_105_, v_inst_106_, v_inst_107_, v_00_u03b2_108_, v_inst_109_, v_inst_110_, v_r_111_, v_aig_112_);
lean_dec_ref(v_inst_110_);
lean_dec_ref(v_inst_109_);
lean_dec_ref(v_inst_107_);
lean_dec_ref(v_inst_106_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___redArg(lean_object* v_r_114_, lean_object* v_entry_115_){
_start:
{
lean_object* v_ref_116_; lean_object* v_aig_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_134_; 
v_ref_116_ = lean_ctor_get(v_entry_115_, 1);
v_aig_117_ = lean_ctor_get(v_entry_115_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_entry_115_);
if (v_isSharedCheck_134_ == 0)
{
v___x_119_ = v_entry_115_;
v_isShared_120_ = v_isSharedCheck_134_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_ref_116_);
lean_inc(v_aig_117_);
lean_dec(v_entry_115_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_134_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v_gate_121_; uint8_t v_invert_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_133_; 
v_gate_121_ = lean_ctor_get(v_ref_116_, 0);
v_invert_122_ = lean_ctor_get_uint8(v_ref_116_, sizeof(void*)*1);
v_isSharedCheck_133_ = !lean_is_exclusive(v_ref_116_);
if (v_isSharedCheck_133_ == 0)
{
v___x_124_ = v_ref_116_;
v_isShared_125_ = v_isSharedCheck_133_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_gate_121_);
lean_dec(v_ref_116_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_133_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = l_Std_Sat_AIG_relabel___redArg(v_r_114_, v_aig_117_);
if (v_isShared_125_ == 0)
{
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_gate_121_);
lean_ctor_set_uint8(v_reuseFailAlloc_132_, sizeof(void*)*1, v_invert_122_);
v___x_128_ = v_reuseFailAlloc_132_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_130_; 
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 1, v___x_128_);
lean_ctor_set(v___x_119_, 0, v___x_126_);
v___x_130_ = v___x_119_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel(lean_object* v_00_u03b1_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_00_u03b2_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_r_141_, lean_object* v_entry_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Std_Sat_AIG_Entrypoint_relabel___redArg(v_r_141_, v_entry_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Entrypoint_relabel___boxed(lean_object* v_00_u03b1_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_00_u03b2_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_r_150_, lean_object* v_entry_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_Sat_AIG_Entrypoint_relabel(v_00_u03b1_144_, v_inst_145_, v_inst_146_, v_00_u03b2_147_, v_inst_148_, v_inst_149_, v_r_150_, v_entry_151_);
lean_dec_ref(v_inst_149_);
lean_dec_ref(v_inst_148_);
lean_dec_ref(v_inst_146_);
lean_dec_ref(v_inst_145_);
return v_res_152_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_Relabel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_Relabel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_Relabel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_Relabel(builtin);
}
#ifdef __cplusplus
}
#endif
