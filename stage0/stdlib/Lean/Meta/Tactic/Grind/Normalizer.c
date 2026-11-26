// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Normalizer
// Imports: public import Lean.Meta.Tactic.Grind.SimpUtil public import Lean.Meta.Tactic.Grind.NormSym import Lean.Meta.Sym.Simp.Main import Lean.Meta.Sym.Util import Lean.Meta.Tactic.Simp.Main
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_Grind_backward_grind_normalizer;
lean_object* l_Lean_Meta_Sym_preprocessExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getNormSymTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkNormSymMethods___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_normalizeImp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_normalizeImp___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_normalizeImp___closed__5;
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_18_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1, &l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1);
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2, &l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2);
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v___x_21_);
lean_ctor_set(v___x_23_, 2, v___x_21_);
lean_ctor_set(v___x_23_, 3, v___x_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0(lean_object* v_e_24_, lean_object* v_config_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Sym_preprocessExpr(v_e_24_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v___x_35_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_a_34_);
lean_dec_ref_known(v___x_33_, 1);
v___x_35_ = l_Lean_Meta_Grind_getNormSymTheorems___redArg(v___y_31_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_37_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_a_36_);
lean_dec_ref_known(v___x_35_, 1);
v___x_37_ = l_Lean_Meta_Grind_mkNormSymMethods___redArg(v_config_25_, v_a_36_, v___y_31_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_a_38_);
lean_dec_ref_known(v___x_37_, 1);
lean_inc(v_a_34_);
v___x_39_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_39_, 0, v_a_34_);
v___x_40_ = ((lean_object*)(l_Lean_Meta_Grind_normalizeImp___lam__0___closed__0));
v___x_41_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3, &l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3);
v___x_42_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_39_, v_a_38_, v___x_40_, v___x_41_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_55_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_55_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_55_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_55_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v_fst_47_; 
v_fst_47_ = lean_ctor_get(v_a_43_, 0);
lean_inc(v_fst_47_);
lean_dec(v_a_43_);
if (lean_obj_tag(v_fst_47_) == 0)
{
lean_object* v___x_49_; 
lean_dec_ref_known(v_fst_47_, 0);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v_a_34_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_34_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
else
{
lean_object* v_e_x27_51_; lean_object* v___x_53_; 
lean_dec(v_a_34_);
v_e_x27_51_ = lean_ctor_get(v_fst_47_, 0);
lean_inc_ref(v_e_x27_51_);
lean_dec_ref_known(v_fst_47_, 2);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v_e_x27_51_);
v___x_53_ = v___x_45_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_e_x27_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
lean_dec(v_a_34_);
v_a_56_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_42_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_42_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
else
{
lean_object* v_a_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_71_; 
lean_dec(v_a_34_);
v_a_64_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_37_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_37_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_69_; 
if (v_isShared_67_ == 0)
{
v___x_69_ = v___x_66_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v_a_64_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
lean_dec(v_a_34_);
lean_dec_ref(v_config_25_);
v_a_72_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_35_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_35_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_dec_ref(v_config_25_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0___boxed(lean_object* v_e_80_, lean_object* v_config_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Meta_Grind_normalizeImp___lam__0(v_e_80_, v_config_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_89_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__0(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1, &l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__0, &l_Lean_Meta_Grind_normalizeImp___closed__0_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__0);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__2(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_unsigned_to_nat(32u);
v___x_96_ = lean_mk_empty_array_with_capacity(v___x_95_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__3(void){
_start:
{
size_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_98_ = ((size_t)5ULL);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_unsigned_to_nat(32u);
v___x_101_ = lean_mk_empty_array_with_capacity(v___x_100_);
v___x_102_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__2, &l_Lean_Meta_Grind_normalizeImp___closed__2_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__2);
v___x_103_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_99_);
lean_ctor_set(v___x_103_, 3, v___x_99_);
lean_ctor_set_usize(v___x_103_, 4, v___x_98_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__4(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__3, &l_Lean_Meta_Grind_normalizeImp___closed__3_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__3);
v___x_105_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__0, &l_Lean_Meta_Grind_normalizeImp___closed__0_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__0);
v___x_106_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
lean_ctor_set(v___x_106_, 2, v___x_105_);
lean_ctor_set(v___x_106_, 3, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__5(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__4, &l_Lean_Meta_Grind_normalizeImp___closed__4_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__4);
v___x_108_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__1, &l_Lean_Meta_Grind_normalizeImp___closed__1_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__1);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* lean_grind_normalize(lean_object* v_e_110_, lean_object* v_config_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_114_);
v___x_118_ = l_Lean_Meta_Grind_backward_grind_normalizer;
v___x_119_ = l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0(v___x_117_, v___x_118_);
lean_dec_ref(v___x_117_);
if (v___x_119_ == 0)
{
lean_object* v___f_120_; lean_object* v___x_121_; 
v___f_120_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_normalizeImp___lam__0___boxed), 9, 2);
lean_closure_set(v___f_120_, 0, v_e_110_);
lean_closure_set(v___f_120_, 1, v_config_111_);
v___x_121_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_120_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Grind_getSimpContext(v_config_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec_ref(v_config_111_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_124_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
v___x_124_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_114_, v_a_115_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = lean_box(0);
v___x_127_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__5, &l_Lean_Meta_Grind_normalizeImp___closed__5_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__5);
v___x_128_ = 0;
v___x_129_ = l_Lean_Meta_simp(v_e_110_, v_a_123_, v_a_125_, v___x_126_, v___x_127_, v___x_128_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_139_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_139_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_139_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_139_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v_fst_134_; lean_object* v_expr_135_; lean_object* v___x_137_; 
v_fst_134_ = lean_ctor_get(v_a_130_, 0);
lean_inc(v_fst_134_);
lean_dec(v_a_130_);
v_expr_135_ = lean_ctor_get(v_fst_134_, 0);
lean_inc_ref(v_expr_135_);
lean_dec(v_fst_134_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 0, v_expr_135_);
v___x_137_ = v___x_132_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_expr_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
v_a_140_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_129_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_129_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v_a_123_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_e_110_);
v_a_148_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_124_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_124_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_e_110_);
v_a_156_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_122_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_122_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___boxed(lean_object* v_e_164_, lean_object* v_config_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = lean_grind_normalize(v_e_164_, v_config_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
return v_res_171_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_NormSym(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Normalizer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_NormSym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Normalizer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_SimpUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_NormSym(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Normalizer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_NormSym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Normalizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Normalizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Normalizer(builtin);
}
#ifdef __cplusplus
}
#endif
