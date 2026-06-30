// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Fin
// Imports: public import Init.Data.Range.Polymorphic.Instances public import Init.Data.Fin.OverflowAware import Init.Grind import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Linear import Init.Data.Option.Lemmas
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNatNat;
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instHasSize___closed__0 = (const lean_object*)&l_Fin_instHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instHasSize(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instHasSize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instHasSize__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instHasSize__1___closed__0 = (const lean_object*)&l_Fin_instHasSize__1___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instHasSize__1(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__2(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0(lean_object* v_n_1_, lean_object* v_i_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_add(v_i_2_, v___x_3_);
v___x_5_ = lean_nat_dec_lt(v___x_4_, v_n_1_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
lean_dec(v___x_4_);
v___x_6_ = lean_box(0);
return v___x_6_;
}
else
{
lean_object* v___x_7_; 
v___x_7_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_4_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0___boxed(lean_object* v_n_8_, lean_object* v_i_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Fin_instUpwardEnumerable___lam__0(v_n_8_, v_i_9_);
lean_dec(v_i_9_);
lean_dec(v_n_8_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1(lean_object* v_n_11_, lean_object* v_m_12_, lean_object* v_i_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = lean_nat_add(v_i_13_, v_m_12_);
v___x_15_ = lean_nat_dec_lt(v___x_14_, v_n_11_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; 
lean_dec(v___x_14_);
v___x_16_ = lean_box(0);
return v___x_16_;
}
else
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_14_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_18_, lean_object* v_m_19_, lean_object* v_i_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Fin_instUpwardEnumerable___lam__1(v_n_18_, v_m_19_, v_i_20_);
lean_dec(v_i_20_);
lean_dec(v_m_19_);
lean_dec(v_n_18_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable(lean_object* v_n_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___f_24_; lean_object* v___x_25_; 
lean_inc(v_n_22_);
v___f_23_ = lean_alloc_closure((void*)(l_Fin_instUpwardEnumerable___lam__0___boxed), 2, 1);
lean_closure_set(v___f_23_, 0, v_n_22_);
v___f_24_ = lean_alloc_closure((void*)(l_Fin_instUpwardEnumerable___lam__1___boxed), 3, 1);
lean_closure_set(v___f_24_, 0, v_n_22_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___f_23_);
lean_ctor_set(v___x_25_, 1, v___f_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Fin_instLeast_x3fOfNatNat(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_box(0);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg(lean_object* v_n_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_mod(v___x_28_, v_n_27_);
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg___boxed(lean_object* v_n_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg(v_n_31_);
lean_dec(v_n_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat(lean_object* v_n_33_, lean_object* v_inst_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg(v_n_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___boxed(lean_object* v_n_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Fin_instLeast_x3fOfNeZeroNat(v_n_36_, v_inst_37_);
lean_dec(v_n_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___lam__0(lean_object* v_lo_39_, lean_object* v_hi_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_hi_40_, v___x_41_);
v___x_43_ = lean_nat_sub(v___x_42_, v_lo_39_);
lean_dec(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___lam__0___boxed(lean_object* v_lo_44_, lean_object* v_hi_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Fin_instHasSize___lam__0(v_lo_44_, v_hi_45_);
lean_dec(v_hi_45_);
lean_dec(v_lo_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize(lean_object* v_n_48_){
_start:
{
lean_object* v___f_49_; 
v___f_49_ = ((lean_object*)(l_Fin_instHasSize___closed__0));
return v___f_49_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___boxed(lean_object* v_n_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Fin_instHasSize(v_n_50_);
lean_dec(v_n_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___lam__0(lean_object* v_lo_52_, lean_object* v_hi_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_unsigned_to_nat(1u);
v___x_55_ = lean_nat_add(v_hi_53_, v___x_54_);
v___x_56_ = lean_nat_sub(v___x_55_, v_lo_52_);
lean_dec(v___x_55_);
v___x_57_ = lean_nat_sub(v___x_56_, v___x_54_);
lean_dec(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___lam__0___boxed(lean_object* v_lo_58_, lean_object* v_hi_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Fin_instHasSize__1___lam__0(v_lo_58_, v_hi_59_);
lean_dec(v_hi_59_);
lean_dec(v_lo_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1(lean_object* v_n_62_){
_start:
{
lean_object* v___f_63_; 
v___f_63_ = ((lean_object*)(l_Fin_instHasSize__1___closed__0));
return v___f_63_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___boxed(lean_object* v_n_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Fin_instHasSize__1(v_n_64_);
lean_dec(v_n_64_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0(lean_object* v_n_66_, lean_object* v_lo_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_nat_sub(v_n_66_, v_lo_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0___boxed(lean_object* v_n_69_, lean_object* v_lo_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Fin_instHasSize__2___lam__0(v_n_69_, v_lo_70_);
lean_dec(v_lo_70_);
lean_dec(v_n_69_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2(lean_object* v_n_72_){
_start:
{
lean_object* v___f_73_; 
v___f_73_ = lean_alloc_closure((void*)(l_Fin_instHasSize__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_73_, 0, v_n_72_);
return v___f_73_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_OverflowAware(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_OverflowAware(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Fin_instLeast_x3fOfNatNat = _init_l_Fin_instLeast_x3fOfNatNat();
lean_mark_persistent(l_Fin_instLeast_x3fOfNatNat);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_OverflowAware(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_OverflowAware(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_Fin(builtin);
}
#ifdef __cplusplus
}
#endif
