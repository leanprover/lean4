// Lean compiler output
// Module: Lean.Data.UnionFind
// Imports: public import Init.Data.Array.Basic import Init.Data.Bool public import Init.Data.Iterators.Basic public import Init.Data.Iterators.Consumers.Monadic.Loop
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_mark_linear(lean_object*);
static const lean_ctor_object l_Lean_UnionFind_instInhabitedNode_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_UnionFind_instInhabitedNode_default___closed__0 = (const lean_object*)&l_Lean_UnionFind_instInhabitedNode_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_UnionFind_instInhabitedNode_default = (const lean_object*)&l_Lean_UnionFind_instInhabitedNode_default___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_instInhabitedNode = (const lean_object*)&l_Lean_UnionFind_instInhabitedNode_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_UnionFind_emptyWithCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_emptyWithCapacity___boxed(lean_object*);
static const lean_array_object l_Lean_UnionFind_instEmptyCollection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_UnionFind_instEmptyCollection___closed__0 = (const lean_object*)&l_Lean_UnionFind_instEmptyCollection___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_UnionFind_instEmptyCollection = (const lean_object*)&l_Lean_UnionFind_instEmptyCollection___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_UnionFind_instInhabited = (const lean_object*)&l_Lean_UnionFind_instEmptyCollection___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_UnionFind_markLinear(lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_size___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_push(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_node(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_node___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_parent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_parent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_rank(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_rank___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_find_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_union_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_root_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_root_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_checkEquiv_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorUnionFindIterNatOfPure___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorUnionFindIterNatOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorUnionFindIterNatOfPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_iterClassM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_iterClassM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_iterClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_UnionFind_emptyWithCapacity(lean_object* v_n_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_mk_empty_array_with_capacity(v_n_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_emptyWithCapacity___boxed(lean_object* v_n_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_UnionFind_emptyWithCapacity(v_n_7_);
lean_dec(v_n_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_markLinear(lean_object* v_uf_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_array_mark_linear(v_uf_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_size(lean_object* v_uf_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_array_get_size(v_uf_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_size___boxed(lean_object* v_uf_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_UnionFind_size(v_uf_17_);
lean_dec_ref(v_uf_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_push(lean_object* v_uf_19_){
_start:
{
lean_object* v_newNode_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_newNode_20_ = lean_array_get_size(v_uf_19_);
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_22_, 0, v_newNode_20_);
lean_ctor_set(v___x_22_, 1, v___x_21_);
lean_ctor_set(v___x_22_, 2, v_newNode_20_);
v___x_23_ = lean_array_push(v_uf_19_, v___x_22_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v_newNode_20_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_node(lean_object* v_uf_25_, lean_object* v_node_26_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_28_ = lean_array_get_borrowed(v___x_27_, v_uf_25_, v_node_26_);
lean_inc(v___x_28_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_node___boxed(lean_object* v_uf_29_, lean_object* v_node_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Data_UnionFind_0__Lean_UnionFind_node(v_uf_29_, v_node_30_);
lean_dec(v_node_30_);
lean_dec_ref(v_uf_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_parent(lean_object* v_uf_32_, lean_object* v_node_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v_parent_36_; 
v___x_34_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_35_ = lean_array_get_borrowed(v___x_34_, v_uf_32_, v_node_33_);
v_parent_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_parent_36_);
return v_parent_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_parent___boxed(lean_object* v_uf_37_, lean_object* v_node_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Data_UnionFind_0__Lean_UnionFind_parent(v_uf_37_, v_node_38_);
lean_dec(v_node_38_);
lean_dec_ref(v_uf_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_rank(lean_object* v_uf_40_, lean_object* v_node_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_rank_44_; 
v___x_42_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_43_ = lean_array_get_borrowed(v___x_42_, v_uf_40_, v_node_41_);
v_rank_44_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_rank_44_);
return v_rank_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_UnionFind_0__Lean_UnionFind_rank___boxed(lean_object* v_uf_45_, lean_object* v_node_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l___private_Lean_Data_UnionFind_0__Lean_UnionFind_rank(v_uf_45_, v_node_46_);
lean_dec(v_node_46_);
lean_dec_ref(v_uf_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_next(lean_object* v_uf_48_, lean_object* v_node_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_next_52_; 
v___x_50_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_51_ = lean_array_get_borrowed(v___x_50_, v_uf_48_, v_node_49_);
v_next_52_ = lean_ctor_get(v___x_51_, 2);
lean_inc(v_next_52_);
return v_next_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_next___boxed(lean_object* v_uf_53_, lean_object* v_node_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_UnionFind_next(v_uf_53_, v_node_54_);
lean_dec(v_node_54_);
lean_dec_ref(v_uf_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_find_x21(lean_object* v_uf_56_, lean_object* v_eqc_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_parent_60_; uint8_t v___x_61_; 
v___x_58_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_59_ = lean_array_get_borrowed(v___x_58_, v_uf_56_, v_eqc_57_);
v_parent_60_ = lean_ctor_get(v___x_59_, 0);
v___x_61_ = lean_nat_dec_eq(v_parent_60_, v_eqc_57_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; uint8_t v___x_63_; 
lean_inc(v_parent_60_);
v___x_62_ = lean_array_get_size(v_uf_56_);
v___x_63_ = lean_nat_dec_lt(v_eqc_57_, v___x_62_);
if (v___x_63_ == 0)
{
lean_dec(v_eqc_57_);
v_eqc_57_ = v_parent_60_;
goto _start;
}
else
{
lean_object* v___x_65_; lean_object* v_parent_66_; lean_object* v_v_67_; lean_object* v_rank_68_; lean_object* v_next_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_80_; 
v___x_65_ = lean_array_get_borrowed(v___x_58_, v_uf_56_, v_parent_60_);
v_parent_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_parent_66_);
v_v_67_ = lean_array_fget(v_uf_56_, v_eqc_57_);
v_rank_68_ = lean_ctor_get(v_v_67_, 1);
v_next_69_ = lean_ctor_get(v_v_67_, 2);
v_isSharedCheck_80_ = !lean_is_exclusive(v_v_67_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v_v_67_, 0);
lean_dec(v_unused_81_);
v___x_71_ = v_v_67_;
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_next_69_);
lean_inc(v_rank_68_);
lean_dec(v_v_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v_xs_x27_74_; lean_object* v___x_76_; 
v___x_73_ = lean_box(0);
v_xs_x27_74_ = lean_array_fset(v_uf_56_, v_eqc_57_, v___x_73_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v_parent_66_);
v___x_76_ = v___x_71_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_parent_66_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_rank_68_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_next_69_);
v___x_76_ = v_reuseFailAlloc_79_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; 
v___x_77_ = lean_array_fset(v_xs_x27_74_, v_eqc_57_, v___x_76_);
lean_dec(v_eqc_57_);
v_uf_56_ = v___x_77_;
v_eqc_57_ = v_parent_60_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_82_, 0, v_uf_56_);
lean_ctor_set(v___x_82_, 1, v_eqc_57_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_union_x21(lean_object* v_uf_83_, lean_object* v_eqc1_84_, lean_object* v_eqc2_85_){
_start:
{
lean_object* v___x_86_; lean_object* v_fst_87_; lean_object* v_snd_88_; lean_object* v___x_89_; lean_object* v_fst_90_; lean_object* v_snd_91_; uint8_t v___x_92_; 
v___x_86_ = l_Lean_UnionFind_find_x21(v_uf_83_, v_eqc1_84_);
v_fst_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_fst_87_);
v_snd_88_ = lean_ctor_get(v___x_86_, 1);
lean_inc(v_snd_88_);
lean_dec_ref(v___x_86_);
v___x_89_ = l_Lean_UnionFind_find_x21(v_fst_87_, v_eqc2_85_);
v_fst_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_fst_90_);
v_snd_91_ = lean_ctor_get(v___x_89_, 1);
lean_inc(v_snd_91_);
lean_dec_ref(v___x_89_);
v___x_92_ = lean_nat_dec_eq(v_snd_88_, v_snd_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_rank_95_; lean_object* v_next_96_; lean_object* v___y_98_; lean_object* v___x_115_; lean_object* v_rank_116_; lean_object* v_next_117_; uint8_t v___x_118_; 
v___x_93_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_94_ = lean_array_get_borrowed(v___x_93_, v_fst_90_, v_snd_88_);
v_rank_95_ = lean_ctor_get(v___x_94_, 1);
v_next_96_ = lean_ctor_get(v___x_94_, 2);
v___x_115_ = lean_array_get_borrowed(v___x_93_, v_fst_90_, v_snd_91_);
v_rank_116_ = lean_ctor_get(v___x_115_, 1);
v_next_117_ = lean_ctor_get(v___x_115_, 2);
v___x_118_ = lean_nat_dec_lt(v_rank_95_, v_rank_116_);
if (v___x_118_ == 0)
{
uint8_t v___x_119_; lean_object* v_offset_120_; lean_object* v___y_122_; lean_object* v___x_140_; uint8_t v___x_141_; 
lean_inc(v_next_117_);
v___x_119_ = lean_nat_dec_eq(v_rank_95_, v_rank_116_);
v_offset_120_ = l_Bool_toNat(v___x_119_);
v___x_140_ = lean_array_get_size(v_fst_90_);
v___x_141_ = lean_nat_dec_lt(v_snd_91_, v___x_140_);
if (v___x_141_ == 0)
{
lean_dec(v_snd_91_);
v___y_122_ = v_fst_90_;
goto v___jp_121_;
}
else
{
lean_object* v_v_142_; lean_object* v_rank_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
lean_inc(v_next_96_);
v_v_142_ = lean_array_fget(v_fst_90_, v_snd_91_);
v_rank_143_ = lean_ctor_get(v_v_142_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_v_142_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; lean_object* v_unused_155_; 
v_unused_154_ = lean_ctor_get(v_v_142_, 2);
lean_dec(v_unused_154_);
v_unused_155_ = lean_ctor_get(v_v_142_, 0);
lean_dec(v_unused_155_);
v___x_145_ = v_v_142_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_rank_143_);
lean_dec(v_v_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v_xs_x27_148_; lean_object* v___x_150_; 
v___x_147_ = lean_box(0);
v_xs_x27_148_ = lean_array_fset(v_fst_90_, v_snd_91_, v___x_147_);
lean_inc(v_snd_88_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 2, v_next_96_);
lean_ctor_set(v___x_145_, 0, v_snd_88_);
v___x_150_ = v___x_145_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_snd_88_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_rank_143_);
lean_ctor_set(v_reuseFailAlloc_152_, 2, v_next_96_);
v___x_150_ = v_reuseFailAlloc_152_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; 
v___x_151_ = lean_array_fset(v_xs_x27_148_, v_snd_91_, v___x_150_);
lean_dec(v_snd_91_);
v___y_122_ = v___x_151_;
goto v___jp_121_;
}
}
}
v___jp_121_:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_array_get_size(v___y_122_);
v___x_124_ = lean_nat_dec_lt(v_snd_88_, v___x_123_);
if (v___x_124_ == 0)
{
lean_dec(v_offset_120_);
lean_dec(v_next_117_);
lean_dec(v_snd_88_);
return v___y_122_;
}
else
{
lean_object* v_v_125_; lean_object* v_parent_126_; lean_object* v_rank_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_138_; 
v_v_125_ = lean_array_fget(v___y_122_, v_snd_88_);
v_parent_126_ = lean_ctor_get(v_v_125_, 0);
v_rank_127_ = lean_ctor_get(v_v_125_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_v_125_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v_v_125_, 2);
lean_dec(v_unused_139_);
v___x_129_ = v_v_125_;
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_rank_127_);
lean_inc(v_parent_126_);
lean_dec(v_v_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v_xs_x27_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_131_ = lean_box(0);
v_xs_x27_132_ = lean_array_fset(v___y_122_, v_snd_88_, v___x_131_);
v___x_133_ = lean_nat_add(v_rank_127_, v_offset_120_);
lean_dec(v_offset_120_);
lean_dec(v_rank_127_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 2, v_next_117_);
lean_ctor_set(v___x_129_, 1, v___x_133_);
v___x_135_ = v___x_129_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_parent_126_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_next_117_);
v___x_135_ = v_reuseFailAlloc_137_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; 
v___x_136_ = lean_array_fset(v_xs_x27_132_, v_snd_88_, v___x_135_);
lean_dec(v_snd_88_);
return v___x_136_;
}
}
}
}
}
else
{
lean_object* v___x_156_; uint8_t v___x_157_; 
lean_inc(v_next_96_);
v___x_156_ = lean_array_get_size(v_fst_90_);
v___x_157_ = lean_nat_dec_lt(v_snd_88_, v___x_156_);
if (v___x_157_ == 0)
{
lean_dec(v_snd_88_);
v___y_98_ = v_fst_90_;
goto v___jp_97_;
}
else
{
lean_object* v_v_158_; lean_object* v_rank_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_169_; 
lean_inc(v_next_117_);
v_v_158_ = lean_array_fget(v_fst_90_, v_snd_88_);
v_rank_159_ = lean_ctor_get(v_v_158_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_v_158_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; lean_object* v_unused_171_; 
v_unused_170_ = lean_ctor_get(v_v_158_, 2);
lean_dec(v_unused_170_);
v_unused_171_ = lean_ctor_get(v_v_158_, 0);
lean_dec(v_unused_171_);
v___x_161_ = v_v_158_;
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_rank_159_);
lean_dec(v_v_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_169_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v_xs_x27_164_; lean_object* v___x_166_; 
v___x_163_ = lean_box(0);
v_xs_x27_164_ = lean_array_fset(v_fst_90_, v_snd_88_, v___x_163_);
lean_inc(v_snd_91_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 2, v_next_117_);
lean_ctor_set(v___x_161_, 0, v_snd_91_);
v___x_166_ = v___x_161_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_snd_91_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_rank_159_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_next_117_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_array_fset(v_xs_x27_164_, v_snd_88_, v___x_166_);
lean_dec(v_snd_88_);
v___y_98_ = v___x_167_;
goto v___jp_97_;
}
}
}
}
v___jp_97_:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_array_get_size(v___y_98_);
v___x_100_ = lean_nat_dec_lt(v_snd_91_, v___x_99_);
if (v___x_100_ == 0)
{
lean_dec(v_next_96_);
lean_dec(v_snd_91_);
return v___y_98_;
}
else
{
lean_object* v_v_101_; lean_object* v_parent_102_; lean_object* v_rank_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_113_; 
v_v_101_ = lean_array_fget(v___y_98_, v_snd_91_);
v_parent_102_ = lean_ctor_get(v_v_101_, 0);
v_rank_103_ = lean_ctor_get(v_v_101_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_v_101_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_v_101_, 2);
lean_dec(v_unused_114_);
v___x_105_ = v_v_101_;
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_rank_103_);
lean_inc(v_parent_102_);
lean_dec(v_v_101_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v_xs_x27_108_; lean_object* v___x_110_; 
v___x_107_ = lean_box(0);
v_xs_x27_108_ = lean_array_fset(v___y_98_, v_snd_91_, v___x_107_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 2, v_next_96_);
v___x_110_ = v___x_105_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_parent_102_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_rank_103_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_next_96_);
v___x_110_ = v_reuseFailAlloc_112_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; 
v___x_111_ = lean_array_fset(v_xs_x27_108_, v_snd_91_, v___x_110_);
lean_dec(v_snd_91_);
return v___x_111_;
}
}
}
}
}
else
{
lean_dec(v_snd_91_);
lean_dec(v_snd_88_);
return v_fst_90_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_root_x21(lean_object* v_uf_172_, lean_object* v_eqc_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_parent_176_; uint8_t v___x_177_; 
v___x_174_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_175_ = lean_array_get_borrowed(v___x_174_, v_uf_172_, v_eqc_173_);
v_parent_176_ = lean_ctor_get(v___x_175_, 0);
v___x_177_ = lean_nat_dec_eq(v_eqc_173_, v_parent_176_);
if (v___x_177_ == 0)
{
v_eqc_173_ = v_parent_176_;
goto _start;
}
else
{
lean_inc(v_eqc_173_);
return v_eqc_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_root_x21___boxed(lean_object* v_uf_179_, lean_object* v_eqc_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_UnionFind_root_x21(v_uf_179_, v_eqc_180_);
lean_dec(v_eqc_180_);
lean_dec_ref(v_uf_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_checkEquiv_x21(lean_object* v_uf_182_, lean_object* v_eqc1_183_, lean_object* v_eqc2_184_){
_start:
{
lean_object* v___x_185_; lean_object* v_fst_186_; lean_object* v_snd_187_; lean_object* v___x_188_; lean_object* v_fst_189_; lean_object* v_snd_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_199_; 
v___x_185_ = l_Lean_UnionFind_find_x21(v_uf_182_, v_eqc1_183_);
v_fst_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_fst_186_);
v_snd_187_ = lean_ctor_get(v___x_185_, 1);
lean_inc(v_snd_187_);
lean_dec_ref(v___x_185_);
v___x_188_ = l_Lean_UnionFind_find_x21(v_fst_186_, v_eqc2_184_);
v_fst_189_ = lean_ctor_get(v___x_188_, 0);
v_snd_190_ = lean_ctor_get(v___x_188_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_199_ == 0)
{
v___x_192_ = v___x_188_;
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snd_190_);
lean_inc(v_fst_189_);
lean_dec(v___x_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = lean_nat_dec_eq(v_snd_187_, v_snd_190_);
lean_dec(v_snd_190_);
lean_dec(v_snd_187_);
v___x_195_ = lean_box(v___x_194_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_195_);
v___x_197_ = v___x_192_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_fst_189_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_195_);
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
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorUnionFindIterNatOfPure___redArg___lam__0(lean_object* v_inst_200_, lean_object* v_it_201_){
_start:
{
lean_object* v_uf_202_; lean_object* v_start_203_; lean_object* v_current_204_; uint8_t v_first_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_229_; 
v_uf_202_ = lean_ctor_get(v_it_201_, 0);
v_start_203_ = lean_ctor_get(v_it_201_, 1);
v_current_204_ = lean_ctor_get(v_it_201_, 2);
v_first_205_ = lean_ctor_get_uint8(v_it_201_, sizeof(void*)*3);
v_isSharedCheck_229_ = !lean_is_exclusive(v_it_201_);
if (v_isSharedCheck_229_ == 0)
{
v___x_207_ = v_it_201_;
v_isShared_208_ = v_isSharedCheck_229_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_current_204_);
lean_inc(v_start_203_);
lean_inc(v_uf_202_);
lean_dec(v_it_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_229_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
uint8_t v___x_209_; 
v___x_209_ = lean_nat_dec_eq(v_current_204_, v_start_203_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_next_212_; lean_object* v___x_214_; 
v___x_210_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_211_ = lean_array_get_borrowed(v___x_210_, v_uf_202_, v_current_204_);
v_next_212_ = lean_ctor_get(v___x_211_, 2);
lean_inc(v_next_212_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 2, v_next_212_);
v___x_214_ = v___x_207_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_uf_202_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_start_203_);
lean_ctor_set(v_reuseFailAlloc_217_, 2, v_next_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_217_, sizeof(void*)*3, v_first_205_);
v___x_214_ = v_reuseFailAlloc_217_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v_current_204_);
v___x_216_ = lean_apply_2(v_inst_200_, lean_box(0), v___x_215_);
return v___x_216_;
}
}
else
{
if (v_first_205_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_del_object(v___x_207_);
lean_dec(v_current_204_);
lean_dec(v_start_203_);
lean_dec_ref(v_uf_202_);
v___x_218_ = lean_box(2);
v___x_219_ = lean_apply_2(v_inst_200_, lean_box(0), v___x_218_);
return v___x_219_;
}
else
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_next_222_; uint8_t v___x_223_; lean_object* v___x_225_; 
v___x_220_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_221_ = lean_array_get_borrowed(v___x_220_, v_uf_202_, v_current_204_);
v_next_222_ = lean_ctor_get(v___x_221_, 2);
lean_inc(v_next_222_);
v___x_223_ = 0;
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 2, v_next_222_);
v___x_225_ = v___x_207_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_uf_202_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_start_203_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_next_222_);
v___x_225_ = v_reuseFailAlloc_228_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*3, v___x_223_);
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_current_204_);
v___x_227_ = lean_apply_2(v_inst_200_, lean_box(0), v___x_226_);
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorUnionFindIterNatOfPure___redArg(lean_object* v_inst_230_){
_start:
{
lean_object* v___f_231_; 
v___f_231_ = lean_alloc_closure((void*)(l_Lean_UnionFind_instIteratorUnionFindIterNatOfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_231_, 0, v_inst_230_);
return v___f_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorUnionFindIterNatOfPure(lean_object* v_m_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v___f_234_; 
v___f_234_ = lean_alloc_closure((void*)(l_Lean_UnionFind_instIteratorUnionFindIterNatOfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_234_, 0, v_inst_233_);
return v___f_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__0(lean_object* v_toPure_235_, lean_object* v_recur_236_, lean_object* v_it_237_, lean_object* v_____do__lift_238_){
_start:
{
if (lean_obj_tag(v_____do__lift_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_240_; 
lean_dec_ref(v_it_237_);
lean_dec(v_recur_236_);
v_a_239_ = lean_ctor_get(v_____do__lift_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v_____do__lift_238_, 1);
v___x_240_ = lean_apply_2(v_toPure_235_, lean_box(0), v_a_239_);
return v___x_240_;
}
else
{
lean_object* v_a_241_; lean_object* v___x_242_; 
lean_dec(v_toPure_235_);
v_a_241_ = lean_ctor_get(v_____do__lift_238_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v_____do__lift_238_, 1);
v___x_242_ = lean_apply_4(v_recur_236_, v_it_237_, v_a_241_, lean_box(0), lean_box(0));
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__1(lean_object* v_toPure_243_, lean_object* v_recur_244_, lean_object* v___y_245_, lean_object* v_acc_246_, lean_object* v_toBind_247_, lean_object* v_s_248_){
_start:
{
switch(lean_obj_tag(v_s_248_))
{
case 0:
{
lean_object* v_it_249_; lean_object* v_out_250_; lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_it_249_ = lean_ctor_get(v_s_248_, 0);
lean_inc(v_it_249_);
v_out_250_ = lean_ctor_get(v_s_248_, 1);
lean_inc(v_out_250_);
lean_dec_ref_known(v_s_248_, 2);
v___f_251_ = lean_alloc_closure((void*)(l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_251_, 0, v_toPure_243_);
lean_closure_set(v___f_251_, 1, v_recur_244_);
lean_closure_set(v___f_251_, 2, v_it_249_);
v___x_252_ = lean_apply_3(v___y_245_, v_out_250_, lean_box(0), v_acc_246_);
v___x_253_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v___x_252_, v___f_251_);
return v___x_253_;
}
case 1:
{
lean_object* v_it_254_; lean_object* v___x_255_; 
lean_dec(v_toBind_247_);
lean_dec(v___y_245_);
lean_dec(v_toPure_243_);
v_it_254_ = lean_ctor_get(v_s_248_, 0);
lean_inc(v_it_254_);
lean_dec_ref_known(v_s_248_, 1);
v___x_255_ = lean_apply_4(v_recur_244_, v_it_254_, v_acc_246_, lean_box(0), lean_box(0));
return v___x_255_;
}
default: 
{
lean_object* v___x_256_; 
lean_dec(v_toBind_247_);
lean_dec(v___y_245_);
lean_dec(v_recur_244_);
v___x_256_ = lean_apply_2(v_toPure_243_, lean_box(0), v_acc_246_);
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__2(lean_object* v_toPure_257_, lean_object* v___y_258_, lean_object* v_toBind_259_, lean_object* v_inst_260_, lean_object* v_lift_261_, lean_object* v_it_262_, lean_object* v_acc_263_, lean_object* v_hP_264_, lean_object* v_recur_265_){
_start:
{
lean_object* v_uf_266_; lean_object* v_start_267_; lean_object* v_current_268_; uint8_t v_first_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_297_; 
v_uf_266_ = lean_ctor_get(v_it_262_, 0);
v_start_267_ = lean_ctor_get(v_it_262_, 1);
v_current_268_ = lean_ctor_get(v_it_262_, 2);
v_first_269_ = lean_ctor_get_uint8(v_it_262_, sizeof(void*)*3);
v_isSharedCheck_297_ = !lean_is_exclusive(v_it_262_);
if (v_isSharedCheck_297_ == 0)
{
v___x_271_ = v_it_262_;
v_isShared_272_ = v_isSharedCheck_297_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_current_268_);
lean_inc(v_start_267_);
lean_inc(v_uf_266_);
lean_dec(v_it_262_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_297_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___f_273_; uint8_t v___x_274_; 
v___f_273_ = lean_alloc_closure((void*)(l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_273_, 0, v_toPure_257_);
lean_closure_set(v___f_273_, 1, v_recur_265_);
lean_closure_set(v___f_273_, 2, v___y_258_);
lean_closure_set(v___f_273_, 3, v_acc_263_);
lean_closure_set(v___f_273_, 4, v_toBind_259_);
v___x_274_ = lean_nat_dec_eq(v_current_268_, v_start_267_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_next_277_; lean_object* v___x_279_; 
v___x_275_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_276_ = lean_array_get_borrowed(v___x_275_, v_uf_266_, v_current_268_);
v_next_277_ = lean_ctor_get(v___x_276_, 2);
lean_inc(v_next_277_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 2, v_next_277_);
v___x_279_ = v___x_271_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_uf_266_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_start_267_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_next_277_);
lean_ctor_set_uint8(v_reuseFailAlloc_283_, sizeof(void*)*3, v_first_269_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_current_268_);
v___x_281_ = lean_apply_2(v_inst_260_, lean_box(0), v___x_280_);
v___x_282_ = lean_apply_4(v_lift_261_, lean_box(0), lean_box(0), v___f_273_, v___x_281_);
return v___x_282_;
}
}
else
{
if (v_first_269_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_del_object(v___x_271_);
lean_dec(v_current_268_);
lean_dec(v_start_267_);
lean_dec_ref(v_uf_266_);
v___x_284_ = lean_box(2);
v___x_285_ = lean_apply_2(v_inst_260_, lean_box(0), v___x_284_);
v___x_286_ = lean_apply_4(v_lift_261_, lean_box(0), lean_box(0), v___f_273_, v___x_285_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_next_289_; uint8_t v___x_290_; lean_object* v___x_292_; 
v___x_287_ = ((lean_object*)(l_Lean_UnionFind_instInhabitedNode_default));
v___x_288_ = lean_array_get_borrowed(v___x_287_, v_uf_266_, v_current_268_);
v_next_289_ = lean_ctor_get(v___x_288_, 2);
lean_inc(v_next_289_);
v___x_290_ = 0;
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 2, v_next_289_);
v___x_292_ = v___x_271_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_uf_266_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_start_267_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_next_289_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*3, v___x_290_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v_current_268_);
v___x_294_ = lean_apply_2(v_inst_260_, lean_box(0), v___x_293_);
v___x_295_ = lean_apply_4(v_lift_261_, lean_box(0), lean_box(0), v___f_273_, v___x_294_);
return v___x_295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__3(lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_lift_300_, lean_object* v_00_u03b3_301_, lean_object* v_Pl_302_, lean_object* v_it_303_, lean_object* v_init_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_toApplicative_306_; lean_object* v_toBind_307_; lean_object* v_toPure_308_; lean_object* v___f_309_; lean_object* v___x_310_; 
v_toApplicative_306_ = lean_ctor_get(v_inst_298_, 0);
lean_inc_ref(v_toApplicative_306_);
v_toBind_307_ = lean_ctor_get(v_inst_298_, 1);
lean_inc(v_toBind_307_);
lean_dec_ref(v_inst_298_);
v_toPure_308_ = lean_ctor_get(v_toApplicative_306_, 1);
lean_inc(v_toPure_308_);
lean_dec_ref(v_toApplicative_306_);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_309_, 0, v_toPure_308_);
lean_closure_set(v___f_309_, 1, v___y_305_);
lean_closure_set(v___f_309_, 2, v_toBind_307_);
lean_closure_set(v___f_309_, 3, v_inst_299_);
lean_closure_set(v___f_309_, 4, v_lift_300_);
v___x_310_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_309_, v_it_303_, v_init_304_, lean_box(0));
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg(lean_object* v_inst_311_, lean_object* v_inst_312_){
_start:
{
lean_object* v___f_313_; 
v___f_313_ = lean_alloc_closure((void*)(l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_313_, 0, v_inst_312_);
lean_closure_set(v___f_313_, 1, v_inst_311_);
return v___f_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad(lean_object* v_m_314_, lean_object* v_n_315_, lean_object* v_inst_316_, lean_object* v_inst_317_){
_start:
{
lean_object* v___f_318_; 
v___f_318_ = lean_alloc_closure((void*)(l_Lean_UnionFind_instIteratorLoopUnionFindIterNatOfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_318_, 0, v_inst_317_);
lean_closure_set(v___f_318_, 1, v_inst_316_);
return v___f_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_iterClassM___redArg(lean_object* v_uf_319_, lean_object* v_eqc_320_){
_start:
{
uint8_t v___x_321_; lean_object* v___x_322_; 
v___x_321_ = 1;
lean_inc(v_eqc_320_);
v___x_322_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_322_, 0, v_uf_319_);
lean_ctor_set(v___x_322_, 1, v_eqc_320_);
lean_ctor_set(v___x_322_, 2, v_eqc_320_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*3, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_iterClassM(lean_object* v_uf_323_, lean_object* v_eqc_324_, lean_object* v_m_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_UnionFind_iterClassM___redArg(v_uf_323_, v_eqc_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_UnionFind_iterClass(lean_object* v_uf_327_, lean_object* v_eqc_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_UnionFind_iterClassM___redArg(v_uf_327_, v_eqc_328_);
return v___x_329_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_UnionFind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_UnionFind(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_UnionFind(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_UnionFind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_UnionFind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_UnionFind(builtin);
}
#ifdef __cplusplus
}
#endif
