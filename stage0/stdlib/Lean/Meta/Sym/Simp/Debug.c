// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Debug
// Imports: public import Lean.Meta.Sym.Simp.Discharger import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.Goal import Lean.Meta.Sym.Util
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_mkSimprocFor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_mkSimprocFor___closed__0;
static lean_once_cell_t l_Lean_Meta_Sym_mkSimprocFor___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_mkSimprocFor___closed__1;
static lean_once_cell_t l_Lean_Meta_Sym_mkSimprocFor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_mkSimprocFor___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkSimprocFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkSimprocFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_mkMethods___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_mkMethods___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_mkMethods___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkMethods___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkMethods___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_mkMethods___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_mkMethods___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_mkMethods___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_mkMethods___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_mkMethods___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_mkMethods___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_mkMethods___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkMethods(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkMethods___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_simpGoalUsing___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_simpGoalUsing___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_simpGoalUsing___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalUsing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalUsing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0(lean_object* v_as_1_, size_t v_sz_2_, size_t v_i_3_, lean_object* v_b_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
uint8_t v___x_10_; 
v___x_10_ = lean_usize_dec_lt(v_i_3_, v_sz_2_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v_b_4_);
return v___x_11_;
}
else
{
lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_12_ = lean_array_uget_borrowed(v_as_1_, v_i_3_);
lean_inc(v_a_12_);
v___x_13_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_a_12_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; size_t v___x_16_; size_t v___x_17_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v___x_13_, 1);
v___x_15_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_4_, v_a_14_);
v___x_16_ = ((size_t)1ULL);
v___x_17_ = lean_usize_add(v_i_3_, v___x_16_);
v_i_3_ = v___x_17_;
v_b_4_ = v___x_15_;
goto _start;
}
else
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_26_; 
lean_dec_ref(v_b_4_);
v_a_19_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_26_ == 0)
{
v___x_21_ = v___x_13_;
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_13_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_a_19_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_sz_2_ = stack[1].m_num;
size_t v_i_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_27_;
v_res_27_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0(v_as_1_, v_sz_2_, v_i_3_, v_b_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0___boxed(lean_object* v_as_28_, lean_object* v_sz_29_, lean_object* v_i_30_, lean_object* v_b_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
size_t v_sz_boxed_37_; size_t v_i_boxed_38_; lean_object* v_res_39_; 
v_sz_boxed_37_ = lean_unbox_usize(v_sz_29_);
lean_dec(v_sz_29_);
v_i_boxed_38_ = lean_unbox_usize(v_i_30_);
lean_dec(v_i_30_);
v_res_39_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0(v_as_28_, v_sz_boxed_37_, v_i_boxed_38_, v_b_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec_ref(v_as_28_);
return v_res_39_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_mkSimprocFor___closed__0(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_mkSimprocFor___closed__1(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_obj_once(&l_Lean_Meta_Sym_mkSimprocFor___closed__0, &l_Lean_Meta_Sym_mkSimprocFor___closed__0_once, _init_l_Lean_Meta_Sym_mkSimprocFor___closed__0);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_mkSimprocFor___closed__2(void){
_start:
{
lean_object* v___x_43_; lean_object* v_thms_44_; 
v___x_43_ = lean_obj_once(&l_Lean_Meta_Sym_mkSimprocFor___closed__1, &l_Lean_Meta_Sym_mkSimprocFor___closed__1_once, _init_l_Lean_Meta_Sym_mkSimprocFor___closed__1);
v_thms_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_thms_44_, 0, v___x_43_);
lean_ctor_set(v_thms_44_, 1, v___x_43_);
return v_thms_44_;
}
}
lean_object* l_Lean_Meta_Sym_mkSimprocFor(lean_object* v_declNames_45_, lean_object* v_d_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_thms_52_; size_t v_sz_53_; size_t v___x_54_; lean_object* v___x_55_; 
v_thms_52_ = lean_obj_once(&l_Lean_Meta_Sym_mkSimprocFor___closed__2, &l_Lean_Meta_Sym_mkSimprocFor___closed__2_once, _init_l_Lean_Meta_Sym_mkSimprocFor___closed__2);
v_sz_53_ = lean_array_size(v_declNames_45_);
v___x_54_ = ((size_t)0ULL);
v___x_55_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_mkSimprocFor_spec__0(v_declNames_45_, v_sz_53_, v___x_54_, v_thms_52_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_64_; 
v_a_56_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_64_ == 0)
{
v___x_58_ = v___x_55_;
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_55_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed), 13, 2);
lean_closure_set(v___x_60_, 0, v_a_56_);
lean_closure_set(v___x_60_, 1, v_d_46_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
lean_dec_ref(v_d_46_);
v_a_65_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_55_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_55_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_mkSimprocFor_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_45_ = stack[0].m_obj;
lean_object* v_d_46_ = stack[1].m_obj;
lean_object* v_a_47_ = stack[2].m_obj;
lean_object* v_a_48_ = stack[3].m_obj;
lean_object* v_a_49_ = stack[4].m_obj;
lean_object* v_a_50_ = stack[5].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lean_Meta_Sym_mkSimprocFor(v_declNames_45_, v_d_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkSimprocFor___boxed(lean_object* v_declNames_74_, lean_object* v_d_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Meta_Sym_mkSimprocFor(v_declNames_74_, v_d_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec_ref(v_declNames_74_);
return v_res_81_;
}
}
lean_object* l_Lean_Meta_Sym_mkMethods___lam__0(lean_object* v_x_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_Meta_Sym_mkMethods___lam__0___closed__0));
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_mkMethods___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_84_ = stack[0].m_obj;
lean_object* v___y_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v___y_90_ = stack[6].m_obj;
lean_object* v___y_91_ = stack[7].m_obj;
lean_object* v___y_92_ = stack[8].m_obj;
lean_object* v___y_93_ = stack[9].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_Lean_Meta_Sym_mkMethods___lam__0(v_x_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkMethods___lam__0___boxed(lean_object* v_x_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Meta_Sym_mkMethods___lam__0(v_x_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v_x_98_);
return v_res_109_;
}
}
lean_object* l_Lean_Meta_Sym_mkMethods(lean_object* v_declNames_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___f_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___f_118_ = ((lean_object*)(l_Lean_Meta_Sym_mkMethods___closed__0));
v___x_119_ = ((lean_object*)(l_Lean_Meta_Sym_mkMethods___closed__1));
v___x_120_ = l_Lean_Meta_Sym_mkSimprocFor(v_declNames_112_, v___x_119_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___f_118_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_120_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_mkMethods_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_112_ = stack[0].m_obj;
lean_object* v_a_113_ = stack[1].m_obj;
lean_object* v_a_114_ = stack[2].m_obj;
lean_object* v_a_115_ = stack[3].m_obj;
lean_object* v_a_116_ = stack[4].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_Meta_Sym_mkMethods(v_declNames_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkMethods___boxed(lean_object* v_declNames_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Sym_mkMethods(v_declNames_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec_ref(v_declNames_139_);
return v_res_145_;
}
}
lean_object* l_Lean_Meta_Sym_simpGoalUsing___lam__0(lean_object* v_declNames_149_, lean_object* v_mvarId_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_Sym_mkMethods(v_declNames_149_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v___x_162_ = ((lean_object*)(l_Lean_Meta_Sym_simpGoalUsing___lam__0___closed__0));
v___x_163_ = l_Lean_Meta_Sym_simpGoal(v_a_161_, v_a_159_, v___x_162_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; lean_object* v___x_165_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
v___x_165_ = l_Lean_Meta_Sym_SimpGoalResult_toOption(v_a_164_, v___y_155_, v___y_156_);
return v___x_165_;
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_163_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_163_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_a_159_);
v_a_174_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_160_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_160_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec(v_mvarId_150_);
v_a_182_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_158_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_158_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_simpGoalUsing___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_149_ = stack[0].m_obj;
lean_object* v_mvarId_150_ = stack[1].m_obj;
lean_object* v___y_151_ = stack[2].m_obj;
lean_object* v___y_152_ = stack[3].m_obj;
lean_object* v___y_153_ = stack[4].m_obj;
lean_object* v___y_154_ = stack[5].m_obj;
lean_object* v___y_155_ = stack[6].m_obj;
lean_object* v___y_156_ = stack[7].m_obj;
lean_object* v_res_190_;
v_res_190_ = l_Lean_Meta_Sym_simpGoalUsing___lam__0(v_declNames_149_, v_mvarId_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
stack->m_obj
 = v_res_190_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalUsing___lam__0___boxed(lean_object* v_declNames_191_, lean_object* v_mvarId_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Meta_Sym_simpGoalUsing___lam__0(v_declNames_191_, v_mvarId_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec_ref(v_declNames_191_);
return v_res_200_;
}
}
lean_object* l_Lean_Meta_Sym_simpGoalUsing(lean_object* v_declNames_201_, lean_object* v_mvarId_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___f_208_; lean_object* v___x_209_; 
v___f_208_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_simpGoalUsing___lam__0___boxed), 9, 2);
lean_closure_set(v___f_208_, 0, v_declNames_201_);
lean_closure_set(v___f_208_, 1, v_mvarId_202_);
v___x_209_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_208_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
return v___x_209_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_simpGoalUsing_0interp(lean_interpreter_value* stack)
{
lean_object* v_declNames_201_ = stack[0].m_obj;
lean_object* v_mvarId_202_ = stack[1].m_obj;
lean_object* v_a_203_ = stack[2].m_obj;
lean_object* v_a_204_ = stack[3].m_obj;
lean_object* v_a_205_ = stack[4].m_obj;
lean_object* v_a_206_ = stack[5].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_Meta_Sym_simpGoalUsing(v_declNames_201_, v_mvarId_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalUsing___boxed(lean_object* v_declNames_211_, lean_object* v_mvarId_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Meta_Sym_simpGoalUsing(v_declNames_211_, v_mvarId_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
return v_res_218_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Debug(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Debug(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Debug(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Debug(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Debug(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Debug(builtin);
}
#ifdef __cplusplus
}
#endif
