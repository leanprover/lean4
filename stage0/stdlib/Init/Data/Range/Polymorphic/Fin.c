// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Fin
// Imports: public import Init.Data.Range.Polymorphic.Instances public import Init.Data.Fin.OverflowAware import Init.Grind import Init.ByCases import Init.Data.Fin.Lemmas import Init.Data.Int.OfNat import Init.Data.Nat.Internal.Linear import Init.Data.Option.Lemmas
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instUpwardEnumerable(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNatNat;
static const lean_ctor_object l_Fin_instLeast_x3fOfNeZeroNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg___closed__0 = (const lean_object*)&l_Fin_instLeast_x3fOfNeZeroNat___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg();
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg___boxed(lean_object*);
static lean_once_cell_t l_Fin_instLeast_x3fOfNeZeroNat___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Fin_instLeast_x3fOfNeZeroNat___closed__0;
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instHasSize___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instHasSize___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instHasSize___redArg___closed__0 = (const lean_object*)&l_Fin_instHasSize___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instHasSize___redArg();
LEAN_EXPORT lean_object* l_Fin_instHasSize___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instHasSize__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instHasSize__1___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instHasSize__1___redArg___closed__0 = (const lean_object*)&l_Fin_instHasSize__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___redArg();
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___redArg___boxed(lean_object*);
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
lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg(){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l_Fin_instLeast_x3fOfNeZeroNat___redArg___closed__0));
return v___x_30_;
}
}
LEAN_EXPORT void l_Fin_instLeast_x3fOfNeZeroNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_31_;
v_res_31_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg();
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___redArg___boxed(lean_object* v___dummy_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg();
return v_res_33_;
}
}
static lean_object* _init_l_Fin_instLeast_x3fOfNeZeroNat___closed__0(void){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Fin_instLeast_x3fOfNeZeroNat___redArg();
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat(lean_object* v_n_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l_Fin_instLeast_x3fOfNeZeroNat___closed__0, &l_Fin_instLeast_x3fOfNeZeroNat___closed__0_once, _init_l_Fin_instLeast_x3fOfNeZeroNat___closed__0);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Fin_instLeast_x3fOfNeZeroNat___boxed(lean_object* v_n_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Fin_instLeast_x3fOfNeZeroNat(v_n_38_, v_inst_39_);
lean_dec(v_n_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___redArg___lam__0(lean_object* v_lo_41_, lean_object* v_hi_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_nat_add(v_hi_42_, v___x_43_);
v___x_45_ = lean_nat_sub(v___x_44_, v_lo_41_);
lean_dec(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___redArg___lam__0___boxed(lean_object* v_lo_46_, lean_object* v_hi_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Fin_instHasSize___redArg___lam__0(v_lo_46_, v_hi_47_);
lean_dec(v_hi_47_);
lean_dec(v_lo_46_);
return v_res_48_;
}
}
lean_object* l_Fin_instHasSize___redArg(){
_start:
{
lean_object* v___f_51_; 
v___f_51_ = ((lean_object*)(l_Fin_instHasSize___redArg___closed__0));
return v___f_51_;
}
}
LEAN_EXPORT void l_Fin_instHasSize___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_52_;
v_res_52_ = l_Fin_instHasSize___redArg();
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___redArg___boxed(lean_object* v___dummy_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Fin_instHasSize___redArg();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize(lean_object* v_n_55_){
_start:
{
lean_object* v___f_56_; 
v___f_56_ = ((lean_object*)(l_Fin_instHasSize___redArg___closed__0));
return v___f_56_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize___boxed(lean_object* v_n_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Fin_instHasSize(v_n_57_);
lean_dec(v_n_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___redArg___lam__0(lean_object* v_lo_59_, lean_object* v_hi_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_hi_60_, v___x_61_);
v___x_63_ = lean_nat_sub(v___x_62_, v_lo_59_);
lean_dec(v___x_62_);
v___x_64_ = lean_nat_sub(v___x_63_, v___x_61_);
lean_dec(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___redArg___lam__0___boxed(lean_object* v_lo_65_, lean_object* v_hi_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Fin_instHasSize__1___redArg___lam__0(v_lo_65_, v_hi_66_);
lean_dec(v_hi_66_);
lean_dec(v_lo_65_);
return v_res_67_;
}
}
lean_object* l_Fin_instHasSize__1___redArg(){
_start:
{
lean_object* v___f_70_; 
v___f_70_ = ((lean_object*)(l_Fin_instHasSize__1___redArg___closed__0));
return v___f_70_;
}
}
LEAN_EXPORT void l_Fin_instHasSize__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_71_;
v_res_71_ = l_Fin_instHasSize__1___redArg();
stack->m_obj
 = v_res_71_;
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___redArg___boxed(lean_object* v___dummy_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Fin_instHasSize__1___redArg();
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1(lean_object* v_n_74_){
_start:
{
lean_object* v___f_75_; 
v___f_75_ = ((lean_object*)(l_Fin_instHasSize__1___redArg___closed__0));
return v___f_75_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__1___boxed(lean_object* v_n_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Fin_instHasSize__1(v_n_76_);
lean_dec(v_n_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0(lean_object* v_n_78_, lean_object* v_lo_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_nat_sub(v_n_78_, v_lo_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2___lam__0___boxed(lean_object* v_n_81_, lean_object* v_lo_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Fin_instHasSize__2___lam__0(v_n_81_, v_lo_82_);
lean_dec(v_lo_82_);
lean_dec(v_n_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Fin_instHasSize__2(lean_object* v_n_84_){
_start:
{
lean_object* v___f_85_; 
v___f_85_ = lean_alloc_closure((void*)(l_Fin_instHasSize__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_85_, 0, v_n_84_);
return v___f_85_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_OverflowAware(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Fin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_OverflowAware(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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
