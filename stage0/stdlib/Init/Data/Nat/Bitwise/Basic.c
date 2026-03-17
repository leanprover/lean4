// Lean compiler output
// Module: Init.Data.Nat.Bitwise.Basic
// Imports: public import Init.Grind.Tactics import Init.Data.Nat.Div.Basic meta import Init.MetaTypes import Init.WFTactics
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_bitwise(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_bitwise___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
lean_object* lean_nat_lxor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_xor___boxed(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_shiftLeft___boxed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Nat_instAndOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_instAndOp___closed__0 = (const lean_object*)&l_Nat_instAndOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_instAndOp = (const lean_object*)&l_Nat_instAndOp___closed__0_value;
static const lean_closure_object l_Nat_instOrOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_instOrOp___closed__0 = (const lean_object*)&l_Nat_instOrOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_instOrOp = (const lean_object*)&l_Nat_instOrOp___closed__0_value;
static const lean_closure_object l_Nat_instXorOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_instXorOp___closed__0 = (const lean_object*)&l_Nat_instXorOp___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_instXorOp = (const lean_object*)&l_Nat_instXorOp___closed__0_value;
static const lean_closure_object l_Nat_instShiftLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_instShiftLeft___closed__0 = (const lean_object*)&l_Nat_instShiftLeft___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_instShiftLeft = (const lean_object*)&l_Nat_instShiftLeft___closed__0_value;
static const lean_closure_object l_Nat_instShiftRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Nat_instShiftRight___closed__0 = (const lean_object*)&l_Nat_instShiftRight___closed__0_value;
LEAN_EXPORT const lean_object* l_Nat_instShiftRight = (const lean_object*)&l_Nat_instShiftRight___closed__0_value;
LEAN_EXPORT uint8_t l_Nat_testBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_testBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_bitwise(lean_object* v_f_1_, lean_object* v_n_2_, lean_object* v_m_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_nat_dec_eq(v_n_2_, v___x_4_);
if (v___x_5_ == 0)
{
uint8_t v___x_6_; 
v___x_6_ = lean_nat_dec_eq(v_m_3_, v___x_4_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v_n_x27_8_; lean_object* v_m_x27_9_; lean_object* v_r_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_7_ = lean_unsigned_to_nat(2u);
v_n_x27_8_ = lean_nat_div(v_n_2_, v___x_7_);
v_m_x27_9_ = lean_nat_div(v_m_3_, v___x_7_);
lean_inc_ref(v_f_1_);
v_r_10_ = l_Nat_bitwise(v_f_1_, v_n_x27_8_, v_m_x27_9_);
lean_dec(v_m_x27_9_);
lean_dec(v_n_x27_8_);
v___x_11_ = lean_nat_mod(v_n_2_, v___x_7_);
v___x_12_ = lean_unsigned_to_nat(1u);
v___x_13_ = lean_nat_dec_eq(v___x_11_, v___x_12_);
lean_dec(v___x_11_);
v___x_14_ = lean_nat_mod(v_m_3_, v___x_7_);
v___x_15_ = lean_nat_dec_eq(v___x_14_, v___x_12_);
lean_dec(v___x_14_);
v___x_16_ = lean_box(v___x_13_);
v___x_17_ = lean_box(v___x_15_);
v___x_18_ = lean_apply_2(v_f_1_, v___x_16_, v___x_17_);
v___x_19_ = lean_unbox(v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; 
v___x_20_ = lean_nat_add(v_r_10_, v_r_10_);
lean_dec(v_r_10_);
return v___x_20_;
}
else
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_nat_add(v_r_10_, v_r_10_);
lean_dec(v_r_10_);
v___x_22_ = lean_nat_add(v___x_21_, v___x_12_);
lean_dec(v___x_21_);
return v___x_22_;
}
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_23_ = lean_box(v___x_6_);
v___x_24_ = lean_box(v___x_5_);
v___x_25_ = lean_apply_2(v_f_1_, v___x_23_, v___x_24_);
v___x_26_ = lean_unbox(v___x_25_);
if (v___x_26_ == 0)
{
return v___x_4_;
}
else
{
lean_inc(v_n_2_);
return v_n_2_;
}
}
}
else
{
uint8_t v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_27_ = 0;
v___x_28_ = lean_box(v___x_27_);
v___x_29_ = lean_box(v___x_5_);
v___x_30_ = lean_apply_2(v_f_1_, v___x_28_, v___x_29_);
v___x_31_ = lean_unbox(v___x_30_);
if (v___x_31_ == 0)
{
return v___x_4_;
}
else
{
lean_inc(v_m_3_);
return v_m_3_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_bitwise___boxed(lean_object* v_f_32_, lean_object* v_n_33_, lean_object* v_m_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Nat_bitwise(v_f_32_, v_n_33_, v_m_34_);
lean_dec(v_m_34_);
lean_dec(v_n_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Nat_land___boxed(lean_object* v_a_00___x40___internal___hyg_38_, lean_object* v_a_00___x40___internal___hyg_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lean_nat_land(v_a_00___x40___internal___hyg_38_, v_a_00___x40___internal___hyg_39_);
lean_dec(v_a_00___x40___internal___hyg_39_);
lean_dec(v_a_00___x40___internal___hyg_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Nat_lor___boxed(lean_object* v_a_00___x40___internal___hyg_43_, lean_object* v_a_00___x40___internal___hyg_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = lean_nat_lor(v_a_00___x40___internal___hyg_43_, v_a_00___x40___internal___hyg_44_);
lean_dec(v_a_00___x40___internal___hyg_44_);
lean_dec(v_a_00___x40___internal___hyg_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Nat_xor___boxed(lean_object* v_a_00___x40___internal___hyg_48_, lean_object* v_a_00___x40___internal___hyg_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lean_nat_lxor(v_a_00___x40___internal___hyg_48_, v_a_00___x40___internal___hyg_49_);
lean_dec(v_a_00___x40___internal___hyg_49_);
lean_dec(v_a_00___x40___internal___hyg_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Nat_shiftLeft___boxed(lean_object* v_a_00___x40___internal___hyg_53_, lean_object* v_a_00___x40___internal___hyg_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = lean_nat_shiftl(v_a_00___x40___internal___hyg_53_, v_a_00___x40___internal___hyg_54_);
lean_dec(v_a_00___x40___internal___hyg_54_);
lean_dec(v_a_00___x40___internal___hyg_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Nat_shiftRight___boxed(lean_object* v_a_00___x40___internal___hyg_58_, lean_object* v_a_00___x40___internal___hyg_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = lean_nat_shiftr(v_a_00___x40___internal___hyg_58_, v_a_00___x40___internal___hyg_59_);
lean_dec(v_a_00___x40___internal___hyg_59_);
lean_dec(v_a_00___x40___internal___hyg_58_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Nat_testBit(lean_object* v_m_71_, lean_object* v_n_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_shiftr(v_m_71_, v_n_72_);
v___x_75_ = lean_nat_land(v___x_73_, v___x_74_);
lean_dec(v___x_74_);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_nat_dec_eq(v___x_75_, v___x_76_);
lean_dec(v___x_75_);
if (v___x_77_ == 0)
{
uint8_t v___x_78_; 
v___x_78_ = 1;
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_testBit___boxed(lean_object* v_m_80_, lean_object* v_n_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Nat_testBit(v_m_80_, v_n_81_);
lean_dec(v_n_81_);
lean_dec(v_m_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Basic(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Bitwise_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
