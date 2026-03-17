// Lean compiler output
// Module: Init.Data.BitVec.Lemmas
// Imports: import all Init.Data.BitVec.Basic import all Init.Data.BitVec.BasicAux public import Init.Data.Fin.Lemmas public import Init.Data.List.BasicAux import Init.Data.List.Lemmas public import Init.Data.BitVec.Basic import Init.ByCases import Init.Data.BitVec.Bootstrap import Init.Data.Int.Bitwise.Lemmas import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.Nat.Div.Lemmas import Init.Data.Nat.MinMax import Init.Data.Nat.Mod import Init.Data.Nat.Simproc import Init.TacticsExtra
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(lean_object* v_x_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_){
_start:
{
lean_object* v_intZero_6_; uint8_t v_isNeg_7_; 
v_intZero_6_ = lean_obj_once(&l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0, &l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___closed__0);
v_isNeg_7_ = lean_int_dec_lt(v_x_3_, v_intZero_6_);
if (v_isNeg_7_ == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; 
lean_dec(v_h__2_5_);
v_a_8_ = lean_nat_abs(v_x_3_);
v___x_9_ = lean_apply_1(v_h__1_4_, v_a_8_);
return v___x_9_;
}
else
{
lean_object* v_abs_10_; lean_object* v_one_11_; lean_object* v_a_12_; lean_object* v___x_13_; 
lean_dec(v_h__1_4_);
v_abs_10_ = lean_nat_abs(v_x_3_);
v_one_11_ = lean_unsigned_to_nat(1u);
v_a_12_ = lean_nat_sub(v_abs_10_, v_one_11_);
lean_dec(v_abs_10_);
v___x_13_ = lean_apply_1(v_h__2_5_, v_a_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg___boxed(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(v_x_14_, v_h__1_15_, v_h__2_16_);
lean_dec(v_x_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___redArg(v_x_19_, v_h__1_20_, v_h__2_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter___boxed(lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Init_Data_BitVec_Lemmas_0__Int_toNat_match__1_splitter(v_motive_23_, v_x_24_, v_h__1_25_, v_h__2_26_);
lean_dec(v_x_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(uint8_t v_x_28_, uint8_t v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_, lean_object* v_h__3_32_, lean_object* v_h__4_33_){
_start:
{
if (v_x_28_ == 0)
{
lean_dec(v_h__4_33_);
lean_dec(v_h__3_32_);
if (v_x_29_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_31_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__1_30_, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_30_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__2_31_, v___x_36_);
return v___x_37_;
}
}
else
{
lean_dec(v_h__2_31_);
lean_dec(v_h__1_30_);
if (v_x_29_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__4_33_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__3_32_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__3_32_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__4_33_, v___x_40_);
return v___x_41_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(lean_object* v_x_42_, lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_, lean_object* v_h__4_47_){
_start:
{
uint8_t v_x_42__boxed_48_; uint8_t v_x_43__boxed_49_; lean_object* v_res_50_; 
v_x_42__boxed_48_ = lean_unbox(v_x_42_);
v_x_43__boxed_49_ = lean_unbox(v_x_43_);
v_res_50_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_42__boxed_48_, v_x_43__boxed_49_, v_h__1_44_, v_h__2_45_, v_h__3_46_, v_h__4_47_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(lean_object* v_motive_51_, uint8_t v_x_52_, uint8_t v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_, lean_object* v_h__3_56_, lean_object* v_h__4_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___redArg(v_x_52_, v_x_53_, v_h__1_54_, v_h__2_55_, v_h__3_56_, v_h__4_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter___boxed(lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_x_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_, lean_object* v_h__3_64_, lean_object* v_h__4_65_){
_start:
{
uint8_t v_x_64__boxed_66_; uint8_t v_x_65__boxed_67_; lean_object* v_res_68_; 
v_x_64__boxed_66_ = lean_unbox(v_x_60_);
v_x_65__boxed_67_ = lean_unbox(v_x_61_);
v_res_68_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_sdiv__eq_match__1_splitter(v_motive_59_, v_x_64__boxed_66_, v_x_65__boxed_67_, v_h__1_62_, v_h__2_63_, v_h__3_64_, v_h__4_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__2_71_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__1_70_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v___x_76_; 
lean_dec(v_h__1_70_);
v_head_74_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_head_74_);
v_tail_75_ = lean_ctor_get(v_x_69_, 1);
lean_inc(v_tail_75_);
lean_dec_ref(v_x_69_);
v___x_76_ = lean_apply_2(v_h__2_71_, v_head_74_, v_tail_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter(lean_object* v_motive_77_, lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_ofBoolListBE_match__1_splitter___redArg(v_x_78_, v_h__1_79_, v_h__2_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(lean_object* v_x_82_, lean_object* v_x_83_, lean_object* v_h__1_84_, lean_object* v_h__2_85_){
_start:
{
lean_object* v_zero_86_; uint8_t v_isZero_87_; 
v_zero_86_ = lean_unsigned_to_nat(0u);
v_isZero_87_ = lean_nat_dec_eq(v_x_82_, v_zero_86_);
if (v_isZero_87_ == 1)
{
lean_object* v___x_88_; 
lean_dec(v_h__2_85_);
v___x_88_ = lean_apply_1(v_h__1_84_, v_x_83_);
return v___x_88_;
}
else
{
lean_object* v_one_89_; lean_object* v_n_90_; lean_object* v___x_91_; 
lean_dec(v_h__1_84_);
v_one_89_ = lean_unsigned_to_nat(1u);
v_n_90_ = lean_nat_sub(v_x_82_, v_one_89_);
v___x_91_ = lean_apply_2(v_h__2_85_, v_n_90_, v_x_83_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg___boxed(lean_object* v_x_92_, lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(v_x_92_, v_x_93_, v_h__1_94_, v_h__2_95_);
lean_dec(v_x_92_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(lean_object* v_w_97_, lean_object* v_motive_98_, lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___redArg(v_x_99_, v_x_100_, v_h__1_101_, v_h__2_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter___boxed(lean_object* v_w_104_, lean_object* v_motive_105_, lean_object* v_x_106_, lean_object* v_x_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_replicate_match__1_splitter(v_w_104_, v_motive_105_, v_x_106_, v_x_107_, v_h__1_108_, v_h__2_109_);
lean_dec(v_x_106_);
lean_dec(v_w_104_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(lean_object* v_x_111_, lean_object* v_x_112_, lean_object* v_h__1_113_, lean_object* v_h__2_114_){
_start:
{
lean_object* v_zero_115_; uint8_t v_isZero_116_; 
v_zero_115_ = lean_unsigned_to_nat(0u);
v_isZero_116_ = lean_nat_dec_eq(v_x_111_, v_zero_115_);
if (v_isZero_116_ == 1)
{
lean_object* v___x_117_; 
lean_dec(v_h__2_114_);
v___x_117_ = lean_apply_1(v_h__1_113_, v_x_112_);
return v___x_117_;
}
else
{
lean_object* v_one_118_; lean_object* v_n_119_; lean_object* v___x_120_; 
lean_dec(v_h__1_113_);
v_one_118_ = lean_unsigned_to_nat(1u);
v_n_119_ = lean_nat_sub(v_x_111_, v_one_118_);
v___x_120_ = lean_apply_2(v_h__2_114_, v_n_119_, v_x_112_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg___boxed(lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_h__1_123_, lean_object* v_h__2_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(v_x_121_, v_x_122_, v_h__1_123_, v_h__2_124_);
lean_dec(v_x_121_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(lean_object* v_motive_126_, lean_object* v_x_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___redArg(v_x_127_, v_x_128_, v_h__1_129_, v_h__2_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter___boxed(lean_object* v_motive_132_, lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Init_Data_BitVec_Lemmas_0__BitVec_reverse_match__1_splitter(v_motive_132_, v_x_133_, v_x_134_, v_h__1_135_, v_h__2_136_);
lean_dec(v_x_133_);
return v_res_137_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Mod(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Mod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_BitVec_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
