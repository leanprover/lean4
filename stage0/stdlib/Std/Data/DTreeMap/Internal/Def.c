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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl_default___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl___redArg___boxed(lean_object*);
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
lean_dec_ref_known(v_t_14_, 5);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl_default___redArg(){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(1);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl_default___redArg___boxed(lean_object* v___dummy_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Std_DTreeMap_Internal_instInhabitedImpl_default___redArg();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl_default(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(1);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl___redArg(){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(1);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl___redArg___boxed(lean_object* v___dummy_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_DTreeMap_Internal_instInhabitedImpl___redArg();
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_instInhabitedImpl(lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(1);
return v___x_71_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_delta(void){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_unsigned_to_nat(3u);
return v___x_72_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_ratio(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_unsigned_to_nat(2u);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___redArg(lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
lean_object* v_size_75_; 
v_size_75_ = lean_ctor_get(v_x_74_, 0);
lean_inc(v_size_75_);
return v_size_75_;
}
else
{
lean_object* v___x_76_; 
v___x_76_ = lean_unsigned_to_nat(0u);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___redArg___boxed(lean_object* v_x_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_DTreeMap_Internal_Impl_size___redArg(v_x_77_);
lean_dec(v_x_77_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v_size_82_; 
v_size_82_ = lean_ctor_get(v_x_81_, 0);
lean_inc(v_size_82_);
return v_size_82_;
}
else
{
lean_object* v___x_83_; 
v___x_83_ = lean_unsigned_to_nat(0u);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_size___boxed(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_DTreeMap_Internal_Impl_size(v_00_u03b1_84_, v_00_u03b2_85_, v_x_86_);
lean_dec(v_x_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___redArg(lean_object* v_x_88_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_k_89_; lean_object* v_v_90_; lean_object* v_l_91_; lean_object* v_r_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_k_89_ = lean_ctor_get(v_x_88_, 1);
v_v_90_ = lean_ctor_get(v_x_88_, 2);
v_l_91_ = lean_ctor_get(v_x_88_, 3);
v_r_92_ = lean_ctor_get(v_x_88_, 4);
v___x_93_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_l_91_);
lean_inc(v_v_90_);
lean_inc(v_k_89_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_k_89_);
lean_ctor_set(v___x_94_, 1, v_v_90_);
v___x_95_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_r_92_);
v___x_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = l_List_appendTR___redArg(v___x_93_, v___x_96_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_box(0);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___redArg___boxed(lean_object* v_x_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_x_99_);
lean_dec(v_x_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_x_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Std_DTreeMap_Internal_Impl_toListModel___redArg(v_x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toListModel___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_DTreeMap_Internal_Impl_toListModel(v_00_u03b1_105_, v_00_u03b2_106_, v_x_107_);
lean_dec(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___redArg(lean_object* v_x_109_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_object* v_l_110_; lean_object* v_r_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_l_110_ = lean_ctor_get(v_x_109_, 3);
v_r_111_ = lean_ctor_get(v_x_109_, 4);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_l_110_);
v___x_114_ = lean_nat_add(v___x_112_, v___x_113_);
lean_dec(v___x_113_);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_r_111_);
v___x_116_ = lean_nat_add(v___x_114_, v___x_115_);
lean_dec(v___x_115_);
lean_dec(v___x_114_);
return v___x_116_;
}
else
{
lean_object* v___x_117_; 
v___x_117_ = lean_unsigned_to_nat(0u);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___redArg___boxed(lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_x_118_);
lean_dec(v_x_118_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize(lean_object* v_00_u03b1_120_, lean_object* v_00_u03b2_121_, lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_DTreeMap_Internal_Impl_treeSize___redArg(v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_treeSize___boxed(lean_object* v_00_u03b1_124_, lean_object* v_00_u03b2_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_DTreeMap_Internal_Impl_treeSize(v_00_u03b1_124_, v_00_u03b2_125_, v_x_126_);
lean_dec(v_x_126_);
return v_res_127_;
}
}
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Def(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
