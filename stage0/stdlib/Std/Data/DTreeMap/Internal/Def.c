// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Def
// Imports: public import Init.Data.SInt.Basic
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
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inner_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inner_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_delta;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_ratio;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorIdx(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Std_DTreeMap_Internal_Impl_ctorIdx___redArg(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorIdx___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Std_DTreeMap_Internal_Impl_ctorIdx(v_00_u03b1_10_, v_00_u03b2_11_, v_x_12_);
lean_dec(v_x_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(lean_object* v_t_14_, lean_object* v_k_15_){
_start:
{
if (lean_obj_tag(v_t_14_) == 0)
{
lean_object* v_size_16_; lean_object* v_k_17_; lean_object* v_v_18_; lean_object* v_l_19_; lean_object* v_r_20_; lean_object* v___x_21_; 
v_size_16_ = lean_ctor_get(v_t_14_, 0);
lean_inc(v_size_16_);
v_k_17_ = lean_ctor_get(v_t_14_, 1);
lean_inc(v_k_17_);
v_v_18_ = lean_ctor_get(v_t_14_, 2);
lean_inc(v_v_18_);
v_l_19_ = lean_ctor_get(v_t_14_, 3);
lean_inc(v_l_19_);
v_r_20_ = lean_ctor_get(v_t_14_, 4);
lean_inc(v_r_20_);
lean_dec_ref(v_t_14_);
v___x_21_ = lean_apply_5(v_k_15_, v_size_16_, v_k_17_, v_v_18_, v_l_19_, v_r_20_);
return v___x_21_;
}
else
{
return v_k_15_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorElim(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_26_, v_k_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_ctorElim___boxed(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_DTreeMap_Internal_Impl_ctorElim(v_00_u03b1_30_, v_00_u03b2_31_, v_motive_32_, v_ctorIdx_33_, v_t_34_, v_h_35_, v_k_36_);
lean_dec(v_ctorIdx_33_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inner_elim___redArg(lean_object* v_t_38_, lean_object* v_inner_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_38_, v_inner_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_inner_elim(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_, lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_inner_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_44_, v_inner_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_leaf_elim___redArg(lean_object* v_t_48_, lean_object* v_leaf_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_48_, v_leaf_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_leaf_elim(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_leaf_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Std_DTreeMap_Internal_Impl_ctorElim___redArg(v_t_54_, v_leaf_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl_default(lean_object* v_00_u03b1_58_, lean_object* v_00_u03b2_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_box(1);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl(lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(1);
return v___x_63_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_delta(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_unsigned_to_nat(3u);
return v___x_64_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_ratio(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(2u);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___redArg(lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v_size_67_; 
v_size_67_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_size_67_);
return v_size_67_;
}
else
{
lean_object* v___x_68_; 
v___x_68_ = lean_unsigned_to_nat(0u);
return v___x_68_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___redArg___boxed(lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_DTreeMap_Internal_Impl_size___redArg(v_x_69_);
lean_dec(v_x_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size(lean_object* v_00_u03b1_71_, lean_object* v_00_u03b2_72_, lean_object* v_x_73_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v_size_74_; 
v_size_74_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_size_74_);
return v_size_74_;
}
else
{
lean_object* v___x_75_; 
v___x_75_ = lean_unsigned_to_nat(0u);
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___boxed(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DTreeMap_Internal_Impl_size(v_00_u03b1_76_, v_00_u03b2_77_, v_x_78_);
lean_dec(v_x_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___redArg(lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_k_81_; lean_object* v_v_82_; lean_object* v_l_83_; lean_object* v_r_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_k_81_ = lean_ctor_get(v_x_80_, 1);
v_v_82_ = lean_ctor_get(v_x_80_, 2);
v_l_83_ = lean_ctor_get(v_x_80_, 3);
v_r_84_ = lean_ctor_get(v_x_80_, 4);
v___x_85_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_83_);
lean_inc(v_v_82_);
lean_inc(v_k_81_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v_k_81_);
lean_ctor_set(v___x_86_, 1, v_v_82_);
v___x_87_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_84_);
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = l_List_appendTR___redArg(v___x_85_, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = lean_box(0);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___redArg___boxed(lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_x_91_);
lean_dec(v_x_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_x_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___boxed(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_DTreeMap_Internal_Impl_toListModel(v_00_u03b1_97_, v_00_u03b2_98_, v_x_99_);
lean_dec(v_x_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___redArg(lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v_l_102_; lean_object* v_r_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_l_102_ = lean_ctor_get(v_x_101_, 3);
v_r_103_ = lean_ctor_get(v_x_101_, 4);
v___x_104_ = lean_unsigned_to_nat(1u);
v___x_105_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_l_102_);
v___x_106_ = lean_nat_add(v___x_104_, v___x_105_);
lean_dec(v___x_105_);
v___x_107_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_r_103_);
v___x_108_ = lean_nat_add(v___x_106_, v___x_107_);
lean_dec(v___x_107_);
lean_dec(v___x_106_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_unsigned_to_nat(0u);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___redArg___boxed(lean_object* v_x_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_x_110_);
lean_dec(v_x_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize(lean_object* v_00_u03b1_112_, lean_object* v_00_u03b2_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___boxed(lean_object* v_00_u03b1_116_, lean_object* v_00_u03b2_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_DTreeMap_Internal_Impl_treeSize(v_00_u03b1_116_, v_00_u03b2_117_, v_x_118_);
lean_dec(v_x_118_);
return v_res_119_;
}
}
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Def(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_DTreeMap_Internal_delta = _init_l_Std_DTreeMap_Internal_delta();
lean_mark_persistent(l_Std_DTreeMap_Internal_delta);
l_Std_DTreeMap_Internal_ratio = _init_l_Std_DTreeMap_Internal_ratio();
lean_mark_persistent(l_Std_DTreeMap_Internal_ratio);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Internal_Def(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Def(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Def(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_Def(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_Def(builtin);
}
#ifdef __cplusplus
}
#endif
