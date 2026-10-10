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
lean_object* l_Lean_Meta_Grind_mkNormSymTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkNormSymMethods(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getSimprocs___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1_ = stack[0].m_obj;
lean_object* v_opt_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0(v_opts_1_, v_opt_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0___boxed(lean_object* v_opts_12_, lean_object* v_opt_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0(v_opts_12_, v_opt_13_);
lean_dec_ref(v_opt_13_);
lean_dec_ref(v_opts_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1, &l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1);
v___x_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2, &l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2_once, _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__2);
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v___x_22_);
lean_ctor_set(v___x_24_, 2, v___x_22_);
lean_ctor_set(v___x_24_, 3, v___x_22_);
return v___x_24_;
}
}
lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0(lean_object* v_e_25_, lean_object* v_config_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Sym_preprocessExpr(v_e_25_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_36_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_a_35_);
lean_dec_ref_known(v___x_34_, 1);
v___x_36_ = l_Lean_Meta_Grind_mkNormSymTheorems(v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_37_);
lean_dec_ref_known(v___x_36_, 1);
v___x_38_ = l_Lean_Meta_Grind_mkNormSymMethods(v_config_26_, v_a_37_);
lean_inc(v_a_35_);
v___x_39_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_39_, 0, v_a_35_);
v___x_40_ = ((lean_object*)(l_Lean_Meta_Grind_normalizeImp___lam__0___closed__0));
v___x_41_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3, &l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__3);
v___x_42_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_39_, v___x_38_, v___x_40_, v___x_41_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
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
lean_ctor_set(v___x_45_, 0, v_a_35_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_35_);
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
lean_dec(v_a_35_);
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
lean_dec(v_a_35_);
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
lean_dec(v_a_35_);
v_a_64_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_71_ == 0)
{
v___x_66_ = v___x_36_;
v_isShared_67_ = v_isSharedCheck_71_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_a_64_);
lean_dec(v___x_36_);
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
return v___x_34_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_normalizeImp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_25_ = stack[0].m_obj;
lean_object* v_config_26_ = stack[1].m_obj;
lean_object* v___y_27_ = stack[2].m_obj;
lean_object* v___y_28_ = stack[3].m_obj;
lean_object* v___y_29_ = stack[4].m_obj;
lean_object* v___y_30_ = stack[5].m_obj;
lean_object* v___y_31_ = stack[6].m_obj;
lean_object* v___y_32_ = stack[7].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Meta_Grind_normalizeImp___lam__0(v_e_25_, v_config_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___lam__0___boxed(lean_object* v_e_73_, lean_object* v_config_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_Grind_normalizeImp___lam__0(v_e_73_, v_config_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec_ref(v_config_74_);
return v_res_82_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1, &l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_normalizeImp___lam__0___closed__1);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__0, &l_Lean_Meta_Grind_normalizeImp___closed__0_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__0);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__2(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_unsigned_to_nat(32u);
v___x_89_ = lean_mk_empty_array_with_capacity(v___x_88_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__3(void){
_start:
{
size_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_91_ = ((size_t)5ULL);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_unsigned_to_nat(32u);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_93_);
v___x_95_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__2, &l_Lean_Meta_Grind_normalizeImp___closed__2_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__2);
v___x_96_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_92_);
lean_ctor_set(v___x_96_, 3, v___x_92_);
lean_ctor_set_usize(v___x_96_, 4, v___x_91_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__4(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__3, &l_Lean_Meta_Grind_normalizeImp___closed__3_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__3);
v___x_98_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__0, &l_Lean_Meta_Grind_normalizeImp___closed__0_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__0);
v___x_99_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
lean_ctor_set(v___x_99_, 2, v___x_98_);
lean_ctor_set(v___x_99_, 3, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_normalizeImp___closed__5(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__4, &l_Lean_Meta_Grind_normalizeImp___closed__4_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__4);
v___x_101_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__1, &l_Lean_Meta_Grind_normalizeImp___closed__1_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__1);
v___x_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
return v___x_102_;
}
}
lean_object* lean_grind_normalize(lean_object* v_e_103_, lean_object* v_config_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_107_);
v___x_111_ = l_Lean_Meta_Grind_backward_grind_normalizer;
v___x_112_ = l_Lean_Option_get___at___00Lean_Meta_Grind_normalizeImp_spec__0(v___x_110_, v___x_111_);
lean_dec_ref(v___x_110_);
if (v___x_112_ == 0)
{
lean_object* v___f_113_; lean_object* v___x_114_; 
v___f_113_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_normalizeImp___lam__0___boxed), 9, 2);
lean_closure_set(v___f_113_, 0, v_e_103_);
lean_closure_set(v___f_113_, 1, v_config_104_);
v___x_114_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_113_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Meta_Grind_getSimpContext(v_config_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec_ref(v_config_104_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_117_, 1);
v___x_119_ = lean_box(0);
v___x_120_ = lean_obj_once(&l_Lean_Meta_Grind_normalizeImp___closed__5, &l_Lean_Meta_Grind_normalizeImp___closed__5_once, _init_l_Lean_Meta_Grind_normalizeImp___closed__5);
v___x_121_ = l_Lean_Meta_simp(v_e_103_, v_a_116_, v_a_118_, v___x_119_, v___x_120_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_131_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_131_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v_fst_126_; lean_object* v_expr_127_; lean_object* v___x_129_; 
v_fst_126_ = lean_ctor_get(v_a_122_, 0);
lean_inc(v_fst_126_);
lean_dec(v_a_122_);
v_expr_127_ = lean_ctor_get(v_fst_126_, 0);
lean_inc_ref(v_expr_127_);
lean_dec(v_fst_126_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v_expr_127_);
v___x_129_ = v___x_124_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_expr_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
v_a_132_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_121_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_121_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec(v_a_116_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec_ref(v_e_103_);
v_a_140_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_117_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_117_);
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
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec_ref(v_e_103_);
v_a_148_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_115_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_115_);
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
}
}
LEAN_EXPORT void lean_grind_normalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_103_ = stack[0].m_obj;
lean_object* v_config_104_ = stack[1].m_obj;
lean_object* v_a_105_ = stack[2].m_obj;
lean_object* v_a_106_ = stack[3].m_obj;
lean_object* v_a_107_ = stack[4].m_obj;
lean_object* v_a_108_ = stack[5].m_obj;
lean_object* v_res_156_;
v_res_156_ = lean_grind_normalize(v_e_103_, v_config_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalizeImp___boxed(lean_object* v_e_157_, lean_object* v_config_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = lean_grind_normalize(v_e_157_, v_config_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
return v_res_164_;
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
